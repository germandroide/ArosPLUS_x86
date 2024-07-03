#include <iostream>
#include <cstdint>
#include <cstring>
#include <cassert>
#include <cmath>
#include <vector>
#include <map>
#include <algorithm>
#include <thread>

#include <proto/exec.h>
#include <proto/dos.h>
#include <proto/graphics.h>
#include <proto/intuition.h>
#include <proto/timer.h>

#include "uae60.h"

// Define los registros del 68060
UAE60_Regs uae60_regs;

// Puntero al inicio de la memoria emulada
uint8_t* amiga_memory_start;

// Puntero al siguiente bloque de memoria libre
uint8_t* amiga_memory_free;

// Estructura para registrar una asignación de memoria
struct MemoryAllocation {
    uae_u32 addr;   // Dirección de inicio
    uae_u32 size;   // Tamaño del bloque
    uae_u32 flags;  // Flags de la asignación
};

// Lista de asignaciones de memoria
std::vector<MemoryAllocation> memory_allocations;

// Código de operación de la última instrucción FPU ejecutada
uint16_t last_fpu_opcode = 0;

// Variable de condición y mutex para la sincronización de excepciones de FPU
std::condition_variable fpu_exception_cv;
std::mutex fpu_exception_mutex;

// Cola de excepciones de la FPU
std::queue<FPUException> fpu_exception_queue;

// Tabla de búsqueda de instrucciones soportadas
bool instruction_supported[65536] = {false};

// Mutex para la emulación de CAS2.L
std::mutex cas2_mutex;

// Mapa de punteros a ViewPorts
std::map<struct ViewPort*, struct ViewPort*> viewport_map;

// Contador de ciclos de renderizado
static uint32_t render_cycle_count = 0;

// Obtiene el siguiente byte de la memoria
uint8_t get_next_byte(uint32_t addr) {
    return (uint8_t)uae60_mem_read(addr, 1);
}

// Obtiene la siguiente word (16 bits) de la memoria
uint16_t get_next_word(uint32_t addr) {
    return (uint16_t)uae60_mem_read(addr, 2);
}

// Obtiene el siguiente long (32 bits) de la memoria
uint32_t get_next_long(uint32_t addr) {
    return uae60_mem_read(addr, 4);
}

// Obtiene el valor del índice
uint32_t get_index_value(uint8_t index_register, uint8_t index_size) {
    if (index_register & 0x08) {
        // Registro de direcciones (A0-A7)
        return uae60_regs.a[index_register & 0x07];
    } else {
        // Registro de datos (D0-D7)
        if (index_size == WORD) {
            // Extender el signo del word a 32 bits
            return (int32_t)(int16_t)uae60_regs.d[index_register];
        } else {
            // Long (32 bits)
            return uae60_regs.d[index_register];
        }
    }
}

// Obtiene el valor de un registro de la FPU del 68060 y lo convierte a double
double get_fp_operand(uint8_t fp_reg) {
    // Obtiene el valor del registro de la FPU
    uint64_t fp_value = *(uint64_t*)(&uae60_regs.fp[fp_reg]);

    // Extrae el signo, el exponente y la mantisa
    uint8_t sign = (fp_value >> 63) & 0x01;
    int16_t exponent = (fp_value >> 48) & 0x7FFF;
    uint64_t mantissa = fp_value & 0xFFFFFFFFFFFF;

    // Convierte al formato IEEE 754 de doble precisión
    double double_value = 0.0;

    if (exponent == 0x7FFF) {
        // Infinito o NaN
        if (mantissa == 0) {
            // Infinito
            double_value = (sign == 0) ? std::numeric_limits<double>::infinity() : -std::numeric_limits<double>::infinity();
        } else {
            // NaN
            double_value = std::numeric_limits<double>::quiet_NaN();
        }
    } else if (exponent == 0) {
        // Cero o número desnormalizado
        if (mantissa == 0) {
            // Cero
            double_value = (sign == 0) ? 0.0 : -0.0;
        } else {
            // Número desnormalizado
            exponent = -16382;  // Exponente para números desnormalizados

            // Normalizar la mantisa
            int shift_count = 0;
            while ((mantissa & 0x8000000000000000ull) == 0) {
                mantissa <<= 1;
                shift_count++;
            }

            // Ajustar el exponente
            exponent -= shift_count;

            // Convertir la mantisa a un valor fraccionario
            double_value = (double)mantissa / (double)(1ull << 64);

            // Aplicar el exponente
            double_value *= std::pow(2.0, exponent);

            // Aplicar el signo
            if (sign == 1) {
                double_value = -double_value;
            }
        }
    } else {
        // Número normalizado
        exponent -= 16383;  // Ajusta el bias del exponente
        mantissa |= 0x10000000000000ull; // Añade el bit implícito

        // Convierte la mantisa a un valor fraccionario
        double_value = (double)mantissa / (double)(1ull << 64);

        // Aplica el exponente
        double_value *= std::pow(2.0, exponent);

        // Aplica el signo
        if (sign == 1) {
            double_value = -double_value;
        }
    }

    return double_value;
}

// Establece el valor de un registro de la FPU del 68060 a partir de un double
uint64_t set_fp_register(double double_value) {
    // Extraer el signo, el exponente y la mantisa del double
    uint64_t bits = *(uint64_t*)(&double_value);
    uint8_t sign = (bits >> 63) & 0x01;
    int16_t exponent = (bits >> 52) & 0x7FF;
    uint64_t mantissa = bits & 0xFFFFFFFFFFFFF;

    // Ajustar el exponente
    exponent += 16383;

    // Combinar el signo, el exponente y la mantisa en un valor de 64 bits
    uint64_t fp_value = ((uint64_t)sign << 63) | ((uint64_t)exponent << 48) | mantissa;

    return fp_value;
}

// Actualiza los flags de la FPU en uae60_regs.fpsr
void update_fpu_flags() {
    uint16_t fpu_status = 0;
    asm("fstsw %0"
        : "=m" (fpu_status));
    uae60_regs.fpsr = (uae60_regs.fpsr & 0xFF00) | (fpu_status & 0xFF);
}

// Manejador de excepciones de la FPU
void fpu_exception_handler() {
    // 1. Obtener el estado de la FPU de x86
    fpu_env_t fpu_env;
    asm("fstenv %0"
        : "=m" (fpu_env));

    // 2. Identificar el tipo de excepción
    uint16_t status_word = fpu_env.status_word;

    // Identificar el tipo de excepción y generar el trap correspondiente
    if (status_word & 0x0001) { uae60_trap(53); }   // Overflow (OVFL)
    if (status_word & 0x0002) { uae60_trap(51); }   // Underflow (UNFL)
    if (status_word & 0x0004) { uae60_trap(50); }   // Divide by Zero (DZ)
    if (status_word & 0x0008) { uae60_trap(52); }   // Invalid Operation (OPERR)
    if (status_word & 0x0010) {
        // Denormalized Operand: registrar un mensaje de advertencia (opcional)
        std::cerr << "Advertencia: Excepción de Operando Desnormalizado en la FPU." << std::endl;
    }
    if (status_word & 0x0020) {
        // Precision Exception: Verificar si es INEX1 o INEX2
        if (last_fpu_opcode == 0xF268 ||  // FINT
            last_fpu_opcode == 0xF278) {  // FINTRZ
            uae60_trap(49); // Genera la excepción INEX1 del 68060
        } else {
            uae60_trap(53); // Genera la excepción INEX2 del 68060
        }
    }
    // if (status_word & 0x0040) { ... }  // Stack Fault (ya manejado con 'finit')

    // Sincronizar con el Core UAE60
    std::unique_lock<std::mutex> lock(fpu_exception_mutex);
    fpu_exception_queue.push({ trap_nr /*, ... */ });
    fpu_exception_cv.notify_one();
}

// Realiza la suma decimal de dos bytes BCD
uint8_t uae60_decimal_add(uint8_t dst, uint8_t src, bool carry_in) {
    uint8_t result = 0;
    bool carry_out = carry_in;

    // Sumar los nibbles bajos
    result = (dst & 0x0F) + (src & 0x0F) + (carry_out ? 1 : 0);
    carry_out = (result > 9);
    result = (result % 10) | (carry_out ? 0x10 : 0);

    // Sumar los nibbles altos
    result |= ((dst & 0xF0) + (src & 0xF0) + (carry_out ? 0x10 : 0)) & 0xF0;
    carry_out = (result > 0x99);

    return result;
}

// Realiza la resta decimal de dos bytes BCD
uint8_t uae60_decimal_subtract(uint8_t dst, uint8_t src, bool borrow_in) {
    uint8_t result = 0;
    bool borrow_out = borrow_in;

    // Restar los nibbles bajos
    int temp = (dst & 0x0F) - (src & 0x0F) - (borrow_out ? 1 : 0);
    if (temp < 0) {
        temp += 10;
        borrow_out = true;
    } else {
        borrow_out = false;
    }
    result = (temp & 0x0F) | (borrow_out ? 0x10 : 0);

    // Restar los nibbles altos
    temp = ((dst & 0xF0) - (src & 0xF0) - (borrow_out ? 0x10 : 0)) & 0xF0;
    if (temp < 0) {
        borrow_out = true;
    }

    result |= temp;

    return result;
}

// Realiza la negación decimal de un byte BCD
uint8_t uae60_decimal_negate(uint8_t dst, bool borrow_in) {
    uint8_t result = 0;
    bool borrow_out = borrow_in;

    // Negar el nibble bajo
    int temp = 9 - (dst & 0x0F) - (borrow_out ? 1 : 0);
    if (temp < 0) {
        temp += 10;
        borrow_out = true;
    } else {
        borrow_out = false;
    }
    result = temp & 0x0F;

    // Negar el nibble alto
    temp = 9 - ((dst & 0xF0) >> 4) - (borrow_out ? 1 : 0);
    result |= (temp << 4) & 0xF0;

    return result;
}

// Función para traducir los flags de memoria de AmigaOS 3.x a AROS x86
uint32_t translate_amiga_mem_flags(uint32_t amiga_flags) {
    uint32_t aros_flags = 0;

    if (amiga_flags & MEMF_CHIP) {
        aros_flags |= AVT_CHIP;
    }
    if (amiga_flags & MEMF_FAST) {
        aros_flags |= AVT_FAST;
    }
    if (amiga_flags & MEMF_ANY) {
        aros_flags |= AVT_ANY;
    }
    if (amiga_flags & MEMF_CLEAR) {
        aros_flags |= AVT_CLEAR;
    }
    if (amiga_flags & MEMF_ALIGN) {
        aros_flags |= AVT_ALIGN | (amiga_flags & 0xFF); // Incluir el límite de alineación
    }

    return aros_flags;
}

// Función para traducir los flags de MsgPort de AmigaOS 3.x a AROS x86
WORD translate_msgport_flags(UBYTE amiga_flags) {
    WORD aros_flags = 0;

    if (amiga_flags & PAF_PUBLIC) {
        aros_flags |= PA_SIGNAL;
    }
    if (amiga_flags & PAF_ALLOWBREAK) {
        aros_flags |= PA_ALLOWBREAK;
    }
    // Otros flags relevantes de AmigaOS 3.x no tienen equivalente directo en AROS x86
    // y se pueden ignorar en esta fase.

    return aros_flags;
}

// Inicializar la tabla de búsqueda de instrucciones
void init_instruction_table() {
    // Grupo 0: Instrucciones de Control de Privilegios
    instruction_supported[0x027C] = true; // ANDI to SR
    instruction_supported[0x007C] = true; // ORI to SR
    instruction_supported[0x0A7C] = true; // EORI to SR
    instruction_supported[0x40C0] = true; // MOVE from SR
    instruction_supported[0x46C0] = true; // MOVE to SR
    instruction_supported[0x4E60] = true; // MOVE USP, An
    instruction_supported[0x4E68] = true; // MOVE An, USP
    instruction_supported[0x4E7A] = true; // MOVEC

    // Grupo 1: Movimiento de Datos
    instruction_supported[0x1000] = true; // MOVE.B
    instruction_supported[0x3000] = true; // MOVE.W
    instruction_supported[0x2000] = true; // MOVE.L
    instruction_supported[0x40D8] = true; // MOVEA.W
    instruction_supported[0x41C0] = true; // LEA
    instruction_supported[0x4840] = true; // SWAP
    instruction_supported[0x4880] = true; // EXT.W
    instruction_supported[0x48C0] = true; // EXT.L
    instruction_supported[0x4E80] = true; // JSR
    instruction_supported[0x4EC0] = true; // JMP
    instruction_supported[0x48D0] = true; // MOVEM.W
    instruction_supported[0x4CD0] = true; // MOVEM.L
    instruction_supported[0x0108] = true; // MOVEP.W
    instruction_supported[0x0118] = true; // MOVEP.L
    instruction_supported[0x0C00] = true; // EXG.L
    instruction_supported[0x7000] = true; // MOVEQ

    // Grupo 2: Aritméticas
    instruction_supported[0x9000] = true; // ADD.B
    instruction_supported[0xB000] = true; // ADD.W
    instruction_supported[0xD000] = true; // ADD.L
    instruction_supported[0x9100] = true; // ADDA.W
    instruction_supported[0xD100] = true; // ADDA.L
    instruction_supported[0x0600] = true; // ADDI.B
    instruction_supported[0x0640] = true; // ADDI.W
    instruction_supported[0x0680] = true; // ADDI.L
    instruction_supported[0x5000] = true; // ADDQ.B
    instruction_supported[0x5040] = true; // ADDQ.W
    instruction_supported[0x5080] = true; // ADDQ.L
    instruction_supported[0x0900] = true; // SUB.B
    instruction_supported[0x0B00] = true; // SUB.W
    instruction_supported[0x0D00] = true; // SUB.L
    instruction_supported[0x9100] = true; // SUBA.W
    instruction_supported[0xD100] = true; // SUBA.L
    instruction_supported[0x0400] = true; // SUBI.B
    instruction_supported[0x0440] = true; // SUBI.W
    instruction_supported[0x0480] = true; // SUBI.L
    instruction_supported[0x5100] = true; // SUBQ.B
    instruction_supported[0x5140] = true; // SUBQ.W
    instruction_supported[0x5180] = true; // SUBQ.L
    instruction_supported[0x4400] = true; // NEG.B
    instruction_supported[0x4600] = true; // NEG.W
    instruction_supported[0x4800] = true; // NEG.L
    instruction_supported[0x4000] = true; // NEGX.B
    instruction_supported[0x4200] = true; // NEGX.W
    instruction_supported[0x4400] = true; // NEGX.L
    instruction_supported[0x4200] = true; // CLR.B
    instruction_supported[0x4400] = true; // CLR.W
    instruction_supported[0x4600] = true; // CLR.L
    instruction_supported[0x4880] = true; // EXT.W
    instruction_supported[0x48C0] = true; // EXT.L
    instruction_supported[0xC1C0] = true; // MULS.W
    instruction_supported[0xC3C0] = true; // MULS.L
    instruction_supported[0xC0C0] = true; // MULU.W
    instruction_supported[0xC2C0] = true; // MULU.L
    instruction_supported[0x81C0] = true; // DIVS.W
    instruction_supported[0x83C0] = true; // DIVS.L
    instruction_supported[0x80C0] = true; // DIVU.W
    instruction_supported[0x82C0] = true; // DIVU.L

    // Grupo 3: Lógicas
    instruction_supported[0xC000] = true; // AND.B
    instruction_supported[0xC040] = true; // AND.W
    instruction_supported[0xC080] = true; // AND.L
    instruction_supported[0x0200] = true; // ANDI.B
    instruction_supported[0x0240] = true; // ANDI.W
    instruction_supported[0x0280] = true; // ANDI.L
    instruction_supported[0x023C] = true; // ANDI to CCR
    instruction_supported[0x027C] = true; // ANDI to SR
    instruction_supported[0x8000] = true; // OR.B
    instruction_supported[0x8040] = true; // OR.W
    instruction_supported[0x8080] = true; // OR.L
    instruction_supported[0x0000] = true; // ORI.B
    instruction_supported[0x0040] = true; // ORI.W
    instruction_supported[0x0080] = true; // ORI.L
    instruction_supported[0x003C] = true; // ORI to CCR
    instruction_supported[0x007C] = true; // ORI to SR
    instruction_supported[0xB100] = true; // EOR.B
    instruction_supported[0xB140] = true; // EOR.W
    instruction_supported[0xB180] = true; // EOR.L
    instruction_supported[0x0A00] = true; // EORI.B
    instruction_supported[0x0A40] = true; // EORI.W
    instruction_supported[0x0A80] = true; // EORI.L
    instruction_supported[0x0A3C] = true; // EORI to CCR
    instruction_supported[0x0A7C] = true; // EORI to SR
    instruction_supported[0x4600] = true; // NOT.B
    instruction_supported[0x4640] = true; // NOT.W
    instruction_supported[0x4680] = true; // NOT.L

    // Grupo 4: Manipulación de Bits
    instruction_supported[0x0800] = true; // BTST
    instruction_supported[0x0840] = true; // BCHG
    instruction_supported[0x0880] = true; // BCLR
    instruction_supported[0x08C0] = true; // BSET
    instruction_supported[0xE100] = true; // ASL.B
    instruction_supported[0xE140] = true; // ASL.W
    instruction_supported[0xE180] = true; // ASL.L
    instruction_supported[0xE000] = true; // ASR.B
    instruction_supported[0xE040] = true; // ASR.W
    instruction_supported[0xE080] = true; // ASR.L
    instruction_supported[0xE100] = true; // LSL.B
    instruction_supported[0xE140] = true; // LSL.W
    instruction_supported[0xE180] = true; // LSL.L
    instruction_supported[0xE000] = true; // LSR.B
    instruction_supported[0xE040] = true; // LSR.W
    instruction_supported[0xE080] = true; // LSR.L
    instruction_supported[0xE100] = true; // ROL.B
    instruction_supported[0xE140] = true; // ROL.W
    instruction_supported[0xE180] = true; // ROL.L
    instruction_supported[0xE000] = true; // ROR.B
    instruction_supported[0xE040] = true; // ROR.W
    instruction_supported[0xE080] = true; // ROR.L
    instruction_supported[0xE100] = true; // ROXL.B
    instruction_supported[0xE140] = true; // ROXL.W
    instruction_supported[0xE180] = true; // ROXL.L
    instruction_supported[0xE000] = true; // ROXR.B
    instruction_supported[0xE040] = true; // ROXR.W
    instruction_supported[0xE080] = true; // ROXR.L

    // Grupo 5: Control de Flujo
    instruction_supported[0x6000] = true; // BRA.W
    instruction_supported[0x60FF] = true; // BRA.L
    instruction_supported[0x6100] = true; // BSR.W
    instruction_supported[0x61FF] = true; // BSR.L
    instruction_supported[0x60] = true;   // BRA.B
    instruction_supported[0x61] = true;   // BSR.B
    instruction_supported[0x64] = true;   // BCC.B - CC
    instruction_supported[0x65] = true;   // BCC.B - CS
    instruction_supported[0x66] = true;   // BCC.B - EQ
    instruction_supported[0x67] = true;   // BCC.B - VS
    instruction_supported[0x68] = true;   // BCC.B - VC
    instruction_supported[0x69] = true;   // BCC.B - HI
    instruction_supported[0x6A] = true;   // BCC.B - LS
    instruction_supported[0x6B] = true;   // BCC.B - GE
    instruction_supported[0x6C] = true;   // BCC.B - LT
    instruction_supported[0x6D] = true;   // BCC.B - GT
    instruction_supported[0x6E] = true;   // BCC.B - LE
    instruction_supported[0x6F] = true;   // BCC.B - NE
    instruction_supported[0x62] = true;   // BCC.B - MI
    instruction_supported[0x63] = true;   // BCC.B - PL
    instruction_supported[0x6400] = true; // BCC.W - CC
    instruction_supported[0x6500] = true; // BCC.W - CS
    instruction_supported[0x6600] = true; // BCC.W - EQ
    instruction_supported[0x6700] = true; // BCC.W - VS
    instruction_supported[0x6800] = true; // BCC.W - VC
    instruction_supported[0x6900] = true; // BCC.W - HI
    instruction_supported[0x6A00] = true; // BCC.W - LS
    instruction_supported[0x6B00] = true; // BCC.W - GE
    instruction_supported[0x6C00] = true; // BCC.W - LT
    instruction_supported[0x6D00] = true; // BCC.W - GT
    instruction_supported[0x6E00] = true; // BCC.W - LE
    instruction_supported[0x6F00] = true; // BCC.W - NE
    instruction_supported[0x6200] = true; // BCC.W - MI
    instruction_supported[0x6300] = true; // BCC.W - PL
    instruction_supported[0x54CC] = true; // DBcc.W - CC
    instruction_supported[0x55CC] = true; // DBcc.W - CS
    instruction_supported[0x56CC] = true; // DBcc.W - EQ
    instruction_supported[0x57CC] = true; // DBcc.W - VS
    instruction_supported[0x58CC] = true; // DBcc.W - VC
    instruction_supported[0x59CC] = true; // DBcc.W - HI
    instruction_supported[0x5ACC] = true; // DBcc.W - LS
    instruction_supported[0x5BCC] = true; // DBcc.W - GE
    instruction_supported[0x5CCC] = true; // DBcc.W - LT
    instruction_supported[0x5DCC] = true; // DBcc.W - GT
    instruction_supported[0x5ECC] = true; // DBcc.W - LE
    instruction_supported[0x5FCC] = true; // DBcc.W - NE
    instruction_supported[0x52CC] = true; // DBcc.W - MI
    instruction_supported[0x53CC] = true; // DBcc.W - PL
    instruction_supported[0x54C8] = true; // Scc - CC
    instruction_supported[0x55C8] = true; // Scc - CS
    instruction_supported[0x56C8] = true; // Scc - EQ
    instruction_supported[0x57C8] = true; // Scc - VS
    instruction_supported[0x58C8] = true; // Scc - VC
    instruction_supported[0x59C8] = true; // Scc - HI
    instruction_supported[0x5AC8] = true; // Scc - LS
    instruction_supported[0x5BC8] = true; // Scc - GE
    instruction_supported[0x5CC8] = true; // Scc - LT
    instruction_supported[0x5DC8] = true; // Scc - GT
    instruction_supported[0x5EC8] = true; // Scc - LE
    instruction_supported[0x5FC8] = true; // Scc - NE
    instruction_supported[0x52C8] = true; // Scc - MI
    instruction_supported[0x53C8] = true; // Scc - PL
    instruction_supported[0x4E40] = true; // TRAP
    instruction_supported[0x4E76] = true; // TRAPV
    instruction_supported[0x4E71] = true; // NOP
    instruction_supported[0x4E73] = true; // RTE
    instruction_supported[0x4E74] = true; // RTR
    instruction_supported[0x4E75] = true; // RTS
    instruction_supported[0x4E50] = true; // LINK
    instruction_supported[0x4E58] = true; // UNLK

    // Grupo 6: Decimal
    instruction_supported[0xC100] = true; // ABCD Dx,Dy
    instruction_supported[0xC108] = true; // ABCD -(Ax),-(Ay)
    instruction_supported[0x8100] = true; // SBCD Dx,Dy
    instruction_supported[0x8108] = true; // SBCD -(Ax),-(Ay)
    instruction_supported[0x4800] = true; // NBCD <ea>

    // Grupo 7: Control del Sistema
    instruction_supported[0x0AC0] = true; // CAS.W
    instruction_supported[0x0ACC] = true; // CAS.L
    instruction_supported[0x0E] = true;   // CAS2.W
    instruction_supported[0x0F] = true;   // CAS2.L
    instruction_supported[0x4180] = true; // CHK.W
    instruction_supported[0x41C0] = true; // CHK.L
    instruction_supported[0x4E70] = true; // RESET
    instruction_supported[0x4E72] = true; // STOP
    instruction_supported[0x41D0] = true; // CHK2.B
    instruction_supported[0x41D8] = true; // CHK2.W
    instruction_supported[0x41DC] = true; // CHK2.L
    instruction_supported[0xB1D0] = true; // CMP2.B
    instruction_supported[0xB1D8] = true; // CMP2.W
    instruction_supported[0xB1DC] = true; // CMP2.L

    // Grupo 9: Coma Flotante (FPU)
    instruction_supported[0xF200] = true; // FADD.S
    instruction_supported[0xF210] = true; // FADD.D
    instruction_supported[0xF220] = true; // FADD.X
    instruction_supported[0xF202] = true; // FSUB.S
    instruction_supported[0xF212] = true; // FSUB.D
    instruction_supported[0xF222] = true; // FSUB.X
    instruction_supported[0xF204] = true; // FMUL.S
    instruction_supported[0xF214] = true; // FMUL.D
    instruction_supported[0xF224] = true; // FMUL.X
    instruction_supported[0xF206] = true; // FDIV.S
    instruction_supported[0xF216] = true; // FDIV.D
    instruction_supported[0xF226] = true; // FDIV.X
    instruction_supported[0xF207] = true; // FSGLDIV
    instruction_supported[0xF205] = true; // FSGLMUL
    instruction_supported[0xF228] = true; // FREM
    instruction_supported[0xF229] = true; // FSCALE
    instruction_supported[0xF208] = true; // FSQRT.S
    instruction_supported[0xF218] = true; // FSQRT.D
    instruction_supported[0xF228] = true; // FSQRT.X
    instruction_supported[0xF209] = true; // FABS.S
    instruction_supported[0xF219] = true; // FABS.D
    instruction_supported[0xF229] = true; // FABS.X
    instruction_supported[0xF230] = true; // FINT.S
    instruction_supported[0xF231] = true; // FINT.D
    instruction_supported[0xF232] = true; // FINT.X
    instruction_supported[0xF234] = true; // FINTRZ.S
    instruction_supported[0xF235] = true; // FINTRZ.D
    instruction_supported[0xF236] = true; // FINTRZ.X
    instruction_supported[0xF23A] = true; // FTST.S
    instruction_supported[0xF23B] = true; // FTST.D
    instruction_supported[0xF23C] = true; // FTST.X
    instruction_supported[0xF200] = true; // FMOVE.S <ea>,FPn
    instruction_supported[0xF210] = true; // FMOVE.D <ea>,FPn
    instruction_supported[0xF220] = true; // FMOVE.X <ea>,FPn
    instruction_supported[0xF201] = true; // FMOVE.S FPn,<ea>
    instruction_supported[0xF211] = true; // FMOVE.D FPn,<ea>
    instruction_supported[0xF221] = true; // FMOVE.X FPn,<ea>
    instruction_supported[0xF240] = true; // FMOVEM.S
    instruction_supported[0xF244] = true; // FMOVEM.D
    instruction_supported[0xF248] = true; // FMOVEM.X
    instruction_supported[0xF310] = true; // FSAVE
    instruction_supported[0xF314] = true; // FRESTORE
    instruction_supported[0xF2C0] = true; // FDBcc.W - F
    instruction_supported[0xF2C1] = true; // FDBcc.W - EQ
    instruction_supported[0xF2C2] = true; // FDBcc.W - OGT
    instruction_supported[0xF2C3] = true; // FDBcc.W - OGE
    instruction_supported[0xF2C4] = true; // FDBcc.W - OLT
    instruction_supported[0xF2C5] = true; // FDBcc.W - OLE
    instruction_supported[0xF2C6] = true; // FDBcc.W - OGL
    instruction_supported[0xF2C7] = true; // FDBcc.W - OR
    instruction_supported[0xF2C8] = true; // FDBcc.W - UN
    instruction_supported[0xF2C9] = true; // FDBcc.W - UEQ
    instruction_supported[0xF2CA] = true; // FDBcc.W - UGT
    instruction_supported[0xF2CB] = true; // FDBcc.W - UGE
    instruction_supported[0xF2CC] = true; // FDBcc.W - ULT
    instruction_supported[0xF2CD] = true; // FDBcc.W - ULE
    instruction_supported[0xF2CE] = true; // FDBcc.W - SF
    instruction_supported[0xF2CF] = true; // FDBcc.W - ST
    instruction_supported[0xF202] = true; // FCMP.S
    instruction_supported[0xF212] = true; // FCMP.D
    instruction_supported[0xF222] = true; // FCMP.X

    // Grupo 10: Instrucciones Complementarias
    instruction_supported[0xF6] = true;    // MOVE16
    instruction_supported[0xF5] = true;    // PERM
    instruction_supported[0x41D0] = true; // CHK2.B
    instruction_supported[0x41D8] = true; // CHK2.W
    instruction_supported[0x41DC] = true; // CHK2.L
    instruction_supported[0xB1D0] = true; // CMP2.B
    instruction_supported[0xB1D8] = true; // CMP2.W
    instruction_supported[0xB1DC] = true; // CMP2.L
    instruction_supported[0x7] = true;    // MOVEQ.L
    instruction_supported[0x4880] = true; // EXTB.L
}

// Inicializar UAE60
void uae60_init() {
    // Inicializa los registros del 68060
    memset(&uae60_regs, 0, sizeof(UAE60_Regs));

    // Obtiene el puntero a la memoria emulada de AmigaOS
    amiga_memory_start = (uint8_t*)uae60_plugin_get_amiga_memory();

    // Inicializar el puntero a la memoria libre
    amiga_memory_free = amiga_memory_start;

    // Inicializar la tabla de búsqueda de instrucciones
    init_instruction_table();

    // Habilitar las excepciones de la FPU
    uint16_t control_word = 0x037F;
    asm("fldcw %0"
        :
        : "m" (control_word));
}

// Ejecuta una instrucción 68060
void uae60_execute(uint16_t opcode) {
    // Decodifica la instrucción
    uint16_t opcode_high = opcode >> 12;
    uint16_t opcode_low = opcode & 0x0FFF;

    // Verificar si la instrucción está soportada por UAE60
    if (!is_instruction_supported(opcode)) {
        // La instrucción no está soportada: redirigir al JIT de AROS x86
        // Obtener la dirección del manejador de la trap correspondiente al opcode
        trap_handler_t trap_handler = get_trap_handler(opcode);

        if (trap_handler != nullptr) {
            // Llamar al manejador de la trap del JIT
            trap_handler(opcode, &uae60_regs); // Pasar el puntero a los registros del 68060
        } else {
            // No se encontró un manejador de trap: generar una excepción
            uae60_trap(4); // Illegal Instruction
        }
    } else {
        // La instrucción está soportada: emularla en UAE60
        switch (opcode_high) {
            case 0x0:  // Grupo 0: Instrucciones de Control de Privilegios
                {
                    // Verificar si estamos en modo supervisor
                    if (!is_supervisor_mode()) {
                        uae60_trap(8); // Genera la excepción Privilege Violation (vector 8)
                        return;        // Sale de la función
                    }

                    switch (opcode) {
                        case 0x027C: // ANDI to SR
                            {
                                uint16_t imm = (uint16_t)get_src_operand(opcode);
                                uae60_regs.sr &= imm;

                                // Actualiza los flags del SR (similar a ANDI to CCR)
                                asm("pushf"         // Guarda los flags actuales en la pila
                                    :
                                    :);
                                asm("pop %%eax"    // Carga los flags en EAX
                                    : "=a" (uae60_regs.sr));

                                // N (Sign Flag - SF)
                                if (uae60_regs.sr & 0x80) {
                                    asm("orl $0x08, %%eax" : : );  // Establece N si el bit 7 es 1
                                } else {
                                    asm("andl $0xFFFFFFF7, %%eax" : : ); // Borra N si el bit 7 es 0
                                }

                                // Z (Zero Flag - ZF)
                                if ((uae60_regs.sr & 0xFF) == 0) {
                                    asm("orl $0x04, %%eax" : : );  // Establece Z si el resultado es 0
                                } else {
                                    asm("andl $0xFFFFFFFB, %%eax" : : ); // Borra Z si el resultado no es 0
                                }

                                // V (Overflow Flag - OF) - Sin cambios para ANDI
                                // C (Carry Flag - CF) - El bit 0 del SR corresponde a C
                                if (uae60_regs.sr & 0x01) {
                                    asm("orl $0x01, %%eax" : : ); // Establece C si el bit 0 es 1
                                } else {
                                    asm("andl $0xFFFFFFFE, %%eax" : : ); // Borra C si el bit 0 es 0
                                }

                                // X (Extend Flag) - El bit 4 del SR corresponde a X
                                if (uae60_regs.sr & 0x10) {
                                    asm("orl $0x10, %%eax" : : ); // Establece X si el bit 4 es 1
                                } else {
                                    asm("andl $0xFFFFFFEF, %%eax" : : ); // Borra X si el bit 4 es 0
                                }

                                asm("push %%eax"   // Guarda los flags actualizados en la pila
                                    :
                                    : "a" (uae60_regs.sr));
                                asm("popf"          // Restaura los flags de la pila
                                    :
                                    :);

                            }
                            break;
                        case 0x007C: // ORI to SR
                            {
                                uint16_t imm = (uint16_t)get_src_operand(opcode);
                                uae60_regs.sr |= imm;
                              // Actualiza los flags del SR (similar a ORI to CCR)
                           asm("pushf"         // Guarda los flags actuales en la pila
                               :
                               :);
                           asm("pop %%eax"    // Carga los flags en EAX
                               : "=a" (uae60_regs.sr));

                           // N (Sign Flag - SF)
                           if (uae60_regs.sr & 0x80) {
                               asm("orl $0x08, %%eax" : : );  // Establece N si el bit 7 es 1
                           } else {
                               asm("andl $0xFFFFFFF7, %%eax" : : ); // Borra N si el bit 7 es 0
                           }

                           // Z (Zero Flag - ZF)
                           if ((uae60_regs.sr & 0xFF) == 0) {
                               asm("orl $0x04, %%eax" : : );  // Establece Z si el resultado es 0
                           } else {
                               asm("andl $0xFFFFFFFB, %%eax" : : ); // Borra Z si el resultado no es 0
                           }

                           // V (Overflow Flag - OF) - Sin cambios para ORI
                           // C (Carry Flag - CF) - El bit 0 del SR corresponde a C
                           if (uae60_regs.sr & 0x01) {
                               asm("orl $0x01, %%eax" : : ); // Establece C si el bit 0 es 1
                           } else {
                               asm("andl $0xFFFFFFFE, %%eax" : : ); // Borra C si el bit 0 es 0
                           }

                           // X (Extend Flag) - El bit 4 del SR corresponde a X
                           if (uae60_regs.sr & 0x10) {
                               asm("orl $0x10, %%eax" : : ); // Establece X si el bit 4 es 1
                           } else {
                               asm("andl $0xFFFFFFEF, %%eax" : : ); // Borra X si el bit 4 es 0
                           }

                           asm("push %%eax"   // Guarda los flags actualizados en la pila
                               :
                               : "a" (uae60_regs.sr));
                           asm("popf"          // Restaura los flags de la pila
                               :
                               :);
// CORTE de error 1
                                // Actualiza los flags del SR (similar a ORI to CCR)
                                asm("pushf"         // Guarda los flags actuales en la pila
                                    :
                                    :);
                                asm("pop %%eax"    // Carga los flags en EAX
                                    : "=a" (uae60_regs.sr));


                                // N (Sign Flag - SF)
                                if (uae60_regs.sr & 0x80) {
                                    asm("orl $0x08, %%eax" : : );  // Establece N si el bit 7 es 1
                                } else {
                                    asm("andl $0xFFFFFFF7, %%eax" : : ); // Borra N si el bit 7 es 0
                                }


                                // Z (Zero Flag - ZF)
                                if ((uae60_regs.sr & 0xFF) == 0) {
                                    asm("orl $0x04, %%eax" : : );  // Establece Z si el resultado es 0
                                } else {
                                    asm("andl $0xFFFFFFFB, %%eax" : : ); // Borra Z si el resultado no es 0
                                }


                                // V (Overflow Flag - OF) - Sin cambios para ORI
                                // C (Carry Flag - CF) - El bit 0 del SR corresponde a C
                                if (uae60_regs.sr & 0x01) {
                                    asm("orl $0x01, %%eax" : : ); // Establece C si el bit 0 es 1
                                } else {
                                    asm("andl $0xFFFFFFFE, %%eax" : : ); // Borra C si el bit 0 es 0
                                }


                                // X (Extend Flag) - El bit 4 del SR corresponde a X
                                if (uae60_regs.sr & 0x10) {
                                    asm("orl $0x10, %%eax" : : ); // Establece X si el bit 4 es 1
                                } else {
                                    asm("andl $0xFFFFFFEF, %%eax" : : ); // Borra X si el bit 4 es 0
                                }

// Corte
                                asm("push %%eax"                                    // Guarda los flags actualizados en la pila
                                    :
                                    : "a" (uae60_regs.sr));
                                asm("popf"          // Restaura los flags de la pila
                                    :
                                    :);
                                break;                          
                            }
                        case 0x0A7C: // EORI to SR
                            {
                                uint16_t imm = (uint16_t)get_src_operand(opcode);
                                uae60_regs.sr ^= imm;


                                // Actualiza los flags del SR (similar a EORI to CCR)
                                asm("pushf"         // Guarda los flags actuales en la pila
                                    :
                                    :);
                                asm("pop %%eax"    // Carga los flags en EAX
                                    : "=a" (uae60_regs.sr));


                                // N (Sign Flag - SF)
                                if (uae60_regs.sr & 0x80) {
                                    asm("orl $0x08, %%eax" : : );  // Establece N si el bit 7 es 1
                                } else {
                                    asm("andl $0xFFFFFFF7, %%eax" : : ); // Borra N si el bit 7 es 0
                                }


                                // Z (Zero Flag - ZF)
                                if ((uae60_regs.sr & 0xFF) == 0) {
                                    asm("orl $0x04, %%eax" : : );  // Establece Z si el resultado es 0
                                } else {
                                    asm("andl $0xFFFFFFFB, %%eax" : : ); // Borra Z si el resultado no es 0
                                }


                                // V (Overflow Flag - OF) - Sin cambios para EORI
                                // C (Carry Flag - CF) - El bit 0 del SR corresponde a C
                                if (uae60_regs.sr & 0x01) {
                                    asm("orl $0x01, %%eax" : : ); // Establece C si el bit 0 es 1
                                } else {
                                    asm("andl $0xFFFFFFFE, %%eax" : : ); // Borra C si el bit 0 es 0
                                }


                                // X (Extend Flag) - El bit 4 del SR corresponde a X
                                if (uae60_regs.sr & 0x10) {
                                    asm("orl $0x10, %%eax" : : ); // Establece X si el bit 4 es 1
                                } else {
                                    asm("andl $0xFFFFFFEF, %%eax" : : ); // Borra X si el bit 4 es 0
                                }


                                asm("push %%eax"   // Guarda los flags actualizados en la pila
                                    :
                                    : "a" (uae60_regs.sr));
                                asm("popf"          // Restaura los flags de la pila
                                    :
                                    :);


                                break;
                            }
                        case 0x40C0: // MOVE from SR
                            {
                                uint32_t dst_addr = get_dst_operand(opcode);
                                // Escribe el valor del SR en la memoria
                                memory[dst_addr] = uae60_regs.sr;
                            }
                            break;
                        case 0x46C0: // MOVE to SR
                            {
                                uint32_t src_addr = get_src_operand(opcode);
                                // Lee el valor del SR de la memoria
                                uae60_regs.sr = memory[src_addr];
                            }
                            break;
case 0x4E60: // MOVE USP,An
                        case 0x4E68: // MOVE An,USP
                            {
                                // Obtener el número de registro de direcciones
                                uint8_t address_register = opcode & 7;

                                // Traducción a x86
                                if (opcode == 0x4E60) {
                                    // MOVE USP,An
                                    asm("movl %%esp, %0"
                                        : "=r" (uae60_regs.a[address_register]));
                                } else {
                                    // MOVE An,USP
                                    asm("movl %0, %%esp"
                                        : 
                                        : "r" (uae60_regs.a[address_register]));
                                }
                                break;
                        case 0x4E7A: // MOVEC
                            {
                                // Obtener el número del registro de control y el registro general
                                uint16_t control_register = get_next_word(uae60_regs.pc);
                                uae60_regs.pc += 2;
                                uint8_t general_register = (opcode >> 9) & 7;


                                // Traducción a x86
                                if ((opcode >> 6) & 1) { // Moviendo de registro de control a registro general
                                    uint32_t control_value = 0;
                                    switch (control_register) {
                                        case 0x000: control_value = uae60_regs.sfc; break;  // SFC
                                        case 0x001: control_value = uae60_regs.dfc; break;  // DFC
                                        case 0x002: control_value = uae60_regs.cacr; break; // CACR
                                        case 0x003: control_value = uae60_regs.usp; break;  // USP
                                        case 0x008: control_value = uae60_regs.vbr; break; // VBR
                                        default:
                                            std::cerr << "Error: MOVEC - Registro de control no válido: " << std::hex << control_register << std::endl;
                                            exit(1);
                                    }
                                    if (general_register < 8) {
                                        uae60_regs.d[general_register] = control_value;
                                    } else {
                                        uae60_regs.a[general_register - 8] = control_value;
                                    }
                                } else { // Moviendo de registro general a registro de control
                                    uint32_t general_value = (general_register < 8) ? uae60_regs.d[general_register]
                                                                                    : uae60_regs.a[general_register - 8];
                                    switch (control_register) {
                                        case 0x000: uae60_regs.sfc = general_value; break;  // SFC
                                        case 0x001: uae60_regs.dfc = general_value; break;  // DFC
                                        case 0x002: uae60_regs.cacr = general_value; break; // CACR
                                        case 0x003: uae60_regs.usp = general_value; break;  // USP
                                        case 0x008: uae60_regs.vbr = general_value; break; // VBR
                                        default:
                                            std::cerr << "Error: MOVEC - Registro de control no válido: " << std::hex << control_register << std::endl;
                                            exit(1);
                                    }
                                }
                                break;
                            }
                    } // switch (opcode)
                }
                break; // case 0x0

            case 0x1:  // Grupo 1: Movimiento de Datos
            case 0x2:  // MOVE.L está en este grupo
            case 0x3:
            case 0x4:
            case 0x7:
                {
                    switch (opcode & 0xFFC0) {
                        case 0x1000: // MOVE.B
                            {
                                uint8_t src = (uint8_t)get_src_operand(opcode);
                                uint32_t dst_addr = get_dst_operand(opcode);
                                amiga_memory[dst_addr] = src;
                                update_flags(src, 1); // Actualiza flags para byte
                            }
                            break;
                        case 0x3000: // MOVE.W
                            {
                                uint16_t src = (uint16_t)get_src_operand(opcode);
                                uint32_t dst_addr = get_dst_operand(opcode);
                                *(uint16_t*)(amiga_memory + dst_addr) = src;
                                update_flags(src, 2); // Actualiza flags para word
                            }
                            break;
                        case 0x2000: // MOVE.L
                            {
                                uint32_t src = get_src_operand(opcode);
                                uint32_t dst_addr = get_dst_operand(opcode);
                                *(uint32_t*)(amiga_memory + dst_addr) = src;
                                update_flags(src, 4); // Actualiza flags para long
                            }
                            break;
                        case 0x40D8: // MOVEA.W
                            {
                                uint16_t src = (uint16_t)get_src_operand(opcode);
                                uint8_t dst_reg = (opcode >> 9) & 7;
                                uae60_regs.a[dst_reg] = (int32_t)(int16_t)src;
                            }
                            break;
                        case 0x41C0: // LEA
                            {
                                uint32_t src = get_src_operand(opcode);
                                uint8_t dst_reg = (opcode >> 9) & 7;
                                uae60_regs.a[dst_reg] = src;
                            }
                            break;
                        case 0x4840: // SWAP
                            {
                                uint8_t reg_num = (opcode >> 9) & 7;
                                uint32_t temp = uae60_regs.d[reg_num];
                                uae60_regs.d[reg_num] = (temp >> 16) | (temp << 16);
                                update_flags(uae60_regs.d[reg_num], 4);
                            }
                            break;
                        case 0x4880: // EXT.W
                            {
                                uint8_t reg_num = (opcode >> 9) & 7;
                                uae60_regs.d[reg_num] = (int32_t)(int16_t)uae60_regs.d[reg_num];
                                update_flags(uae60_regs.d[reg_num], 4);
                            }
                            break;
                        case 0x48C0: // EXT.L
                            {
                                uint8_t reg_num = (opcode >> 9) & 7;
                                update_flags(uae60_regs.d[reg_num], 4);
                            }
                            break;
                        case 0x4E80: // JSR
                            {
                                uint32_t src_addr = get_src_operand(opcode);
                                uae60_regs.a[7] -= 4;
                                *(uint32_t*)(amiga_memory + uae60_regs.a[7]) = uae60_regs.pc;
                                uae60_regs.pc = src_addr;
                            }
                            break;
                        case 0x4EC0: // JMP
                            {
                                uint32_t src_addr = get_src_operand(opcode);
                                uae60_regs.pc = src_addr;
                            }
                            break;
                        case 0x48D0: // MOVEM.W (registros a memoria)
                            {
                                uint16_t register_list = get_next_word(uae60_regs.pc);
                                uae60_regs.pc += 2;
                                uint32_t dst_addr = get_dst_operand(opcode);
                                for (int i = 0; i < 16; ++i) {
                                    if (register_list & (1 << i)) {
                                        uint16_t value = (i < 8) ? uae60_regs.d[i] & 0xFFFF : uae60_regs.a[i - 8] & 0xFFFF;
                                        *(uint16_t*)(amiga_memory + dst_addr) = value;
                                        dst_addr += 2;
                                    }
                                }
                            }
                            break;
                        case 0x4CD0: // MOVEM.L (registros a memoria)
                            {
                                uint16_t register_list = get_next_word(uae60_regs.pc);
                                uae60_regs.pc += 2;
                                uint32_t dst_addr = get_dst_operand(opcode);
                                for (int i = 0; i < 16; ++i) {
                                    if (register_list & (1 << i)) {
                                        uint32_t value = (i < 8) ? uae60_regs.d[i] : uae60_regs.a[i - 8];
                                        *(uint32_t*)(amiga_memory + dst_addr) = value;
                                        dst_addr += 4;
                                    }
                                }
                            }
                            break;
                        case 0x4890: // MOVEM.W (memoria a registros)
                            {
                                uint16_t register_list = get_next_word(uae60_regs.pc);
                                uae60_regs.pc += 2;
                                uint32_t src_addr = get_src_operand(opcode);
                                for (int i = 0; i < 16; ++i) {
                                    if (register_list & (1 << i)) {
                                        uint16_t value = *(uint16_t*)(amiga_memory + src_addr);
                                        if (i < 8) {
                                            uae60_regs.d[i] = (uae60_regs.d[i] & 0xFFFF0000) | value;
                                        } else {
                                            uae60_regs.a[i - 8] = (uae60_regs.a[i - 8] & 0xFFFF0000) | value;
                                        }
                                        src_addr += 2;
                                    }
                                }
                            }
                            break;
                        case 0x4C90: // MOVEM.L (memoria a registros)
                            {
                                uint16_t register_list = get_next_word(uae60_regs.pc);
                                uae60_regs.pc += 2;
                                uint32_t src_addr = get_src_operand(opcode);
                                for (int i = 0; i < 16; ++i) {
                                    if (register_list & (1 << i)) {
                                        uint32_t value = *(uint32_t*)(amiga_memory + src_addr);
                                        if (i < 8) {
                                            uae60_regs.d[i] = value;
                                        } else {
                                            uae60_regs.a[i - 8] = value;
                                        }
                                        src_addr += 4;
                                    }
                                }
                            }
                            break;
                        case 0x0108: // MOVEP.W
                            {
                                uint8_t data_reg = (opcode >> 9) & 7;
                                uint16_t displacement = get_next_word(uae60_regs.pc);
                                uae60_regs.pc += 2;
                                uint32_t addr_reg = opcode & 7;
                                uint32_t addr = uae60_regs.a[addr_reg] + displacement;
                                if ((opcode >> 6) & 1) { // Transferencia de registro a memoria
                                    uint16_t value = uae60_regs.d[data_reg];
                                    memory[addr] = value & 0xFF;
                                    memory[addr + 2] = (value >> 8) & 0xFF;
                                }
                                else { // Transferencia de memoria a registro
                                    uint16_t value = memory[addr] | (memory[addr + 2] << 8);
                                    uae60_regs.d[data_reg] = (uae60_regs.d[data_reg] & 0xFFFF0000) | value;
                                }
                            }
                            break;
                        case 0x0118: // MOVEP.L
                            {
                                uint8_t data_reg = (opcode >> 9) & 7;
                                uint16_t displacement = get_next_word(uae60_regs.pc);
                                uae60_regs.pc += 2;
                                uint32_t addr_reg = opcode & 7;
                                uint32_t addr = uae60_regs.a[addr_reg] + displacement;
                                if ((opcode >> 6) & 1) { // Transferencia de registro a memoria
                                    uint32_t value = uae60_regs.d[data_reg];
                                    memory[addr] = value & 0xFF;
                                    memory[addr + 2] = (value >> 8) & 0xFF;
                                    memory[addr + 4] = (value >> 16) & 0xFF;
                                    memory[addr + 6] = (value >> 24) & 0xFF;
                                }
                                else { // Transferencia de memoria a registro
                                    uint32_t value = memory[addr] | (memory[addr + 2] << 8) | (memory[addr + 4] << 16) | (memory[addr + 6] << 24);
                                    uae60_regs.d[data_reg] = value;
                                }
                            }
                            break;
                        case 0x0C00: // EXG.L
                            {
                                uint8_t reg1 = (opcode >> 9) & 7;
                                uint8_t reg2 = opcode & 7;
                                std::swap(uae60_regs.d[reg1], uae60_regs.d[reg2]);
                            }
                            break;
                        case 0x7000: // MOVEQ
                            {
                                uint8_t reg = (opcode >> 9) & 7;
                                uint32_t data = (int32_t)(int8_t)(opcode & 0xFF);
                                uae60_regs.d[reg] = data;
                                update_flags(uae60_regs.d[reg], 4);
                            }
                    } // switch (opcode & 0xFFC0)
                }
                break; // case 0x1, 0x2, 0x3, 0x4, 0x7

            case 0x5:  // Grupo 5: ADDQ, SUBQ, Scc, DBcc
                {
                    switch (opcode & 0xF000) {
                        case 0x5000: // ADDQ
                            {
                                uint8_t data = (opcode >> 9) & 7;
                                if (data == 0) data = 8;
                                uint32_t src = get_src_operand(opcode);
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint32_t result;

                                switch (opcode & 0x00C0) {
                                    case 0x00C0: // Long
                                        result = src + data;
                                        *(uint32_t*)(amiga_memory + dst_addr) = result;
                                        update_flags(result, 4);
                                        break;
                                    case 0x0080: // Word
                                        result = (src & 0xFFFF) + data;
                                        *(uint16_t*)(amiga_memory + dst_addr) = (uint16_t)result;
                                        update_flags(result, 2);
                                        break;
                                    case 0x0040: // Byte
                                        result = (src & 0xFF) + data;
                                        amiga_memory[dst_addr] = (uint8_t)result;
                                        update_flags(result, 1);
                                        break;
                                }
                            }
                            break;
                        case 0x5100: // SUBQ
                            {
                                uint8_t data = (opcode >> 9) & 7;
                                if (data == 0) data = 8;
                                uint32_t src = get_src_operand(opcode);
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint32_t result;

                                switch (opcode & 0x00C0) {
                                    case 0x00C0: // Long
                                        result = src - data;
                                        *(uint32_t*)(amiga_memory + dst_addr) = result;
                                        update_flags(result, 4);
                                        break;
                                    case 0x0080: // Word
                                        result = (src & 0xFFFF) - data;
                                        *(uint16_t*)(amiga_memory + dst_addr) = (uint16_t)result;
                                        update_flags(result, 2);
                                        break;
                                    case 0x0040: // Byte
                                        result = (src & 0xFF) - data;
                                        amiga_memory[dst_addr] = (uint8_t)result;
                                        update_flags(result, 1);
                                        break;
                                }
                            }
                            break;
                        case 0x54C8: // Scc
                            {
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint8_t condition = (opcode >> 8) & 0xF;
                                bool result = false;
                                switch (condition) {
                                    case 0x4: result = (uae60_regs.sr & 0x01) == 0; break;  // CC - Carry Clear
                                    case 0x5: result = (uae60_regs.sr & 0x01) != 0; break;  // CS - Carry Set
                                    case 0x6: result = (uae60_regs.sr & 0x04) != 0; break;  // EQ - Equal
                                    case 0x7: result = (uae60_regs.sr & 0x02) != 0; break;  // VS - Overflow Set
                                    case 0x8: result = (uae60_regs.sr & 0x02) == 0; break;  // VC - Overflow Clear
                                    case 0x9: result = (uae60_regs.sr & 0x8000) == 0 && (uae60_regs.sr & 0x4000) != 0; break; // HI - Higher
                                    case 0xA: result = (uae60_regs.sr & 0x8000) != 0 || (uae60_regs.sr & 0x4000) == 0; break; // LS - Lower or Same
                                    case 0xB: result = (uae60_regs.sr & 0x8000) == (uae60_regs.sr & 0x0001); break; // GE - Greater or Equal
                                    case 0xC: result = (uae60_regs.sr & 0x8000) != (uae60_regs.sr & 0x0001); break; // LT - Less Than
                                    case 0xD: result = (uae60_regs.sr & 0x8000) == 0; break; // GT - Greater Than
                                    case 0xE: result = (uae60_regs.sr & 0x8000) != 0; break; // LE - Less or Equal
                                    case 0xF: result = (uae60_regs.sr & 0x04) == 0; break;  // NE - Not Equal
                                    case 0x2: result = (uae60_regs.sr & 0x08) != 0; break;  // MI - Minus
                                    case 0x3: result = (uae60_regs.sr & 0x08) == 0; break;  // PL - Plus
                                }
                                amiga_memory[dst_addr] = result ? 0xFF : 0x00;
                            }
                            break;
                        case 0x54CC:  // DBcc.W - CC
                        case 0x55CC:  // DBcc.W - CS
                        case 0x56CC:  // DBcc.W - EQ
                        case 0x57CC:  // DBcc.W - VS
                        case 0x58CC:  // DBcc.W - VC
                        case 0x59CC:  // DBcc.W - HI
                        case 0x5ACC:  // DBcc.W - LS
                        case 0x5BCC:  // DBcc.W - GE
                        case 0x5CCC:  // DBcc.W - LT
                        case 0x5DCC:  // DBcc.W - GT
                        case 0x5ECC:  // DBcc.W - LE
                        case 0x5FCC:  // DBcc.W - NE
                        case 0x52CC:  // DBcc.W - MI
                        case 0x53CC:  // DBcc.W - PL
                            {
                                uint8_t data_reg = (opcode >> 9) & 7;
                                int16_t displacement = (int16_t)get_next_word(uae60_regs.pc);
                                uae60_regs.pc += 2;
                                --uae60_regs.d[data_reg];
                                uint8_t condition = (opcode >> 8) & 0xF;
                                bool shouldBranch = false;
                                switch (condition) {
                                    case 0x4: shouldBranch = (uae60_regs.sr & 0x01) != 0; break;  // DBCC - Carry Clear
                                    case 0x5: shouldBranch = (uae60_regs.sr & 0x01) == 0; break;  // DBCS - Carry Set
                                    case 0x6: shouldBranch = (uae60_regs.sr & 0x04) == 0; break;  // DBEQ - Equal
                                    case 0x7: shouldBranch = (uae60_regs.sr & 0x02) == 0; break;  // DBVS - Overflow Set
                                    case 0x8: shouldBranch = (uae60_regs.sr & 0x02) != 0; break;  // DBVC - Overflow Clear
                                    case 0x9: shouldBranch = (uae60_regs.sr & 0x8000) != 0 || (uae60_regs.sr & 0x4000) == 0; break; // DBHI - Higher
                                    case 0xA: shouldBranch = (uae60_regs.sr & 0x8000) == 0 && (uae60_regs.sr & 0x4000) != 0; break; // DBLS - Lower or Same
                                    case 0xB: shouldBranch = (uae60_regs.sr & 0x8000) != (uae60_regs.sr & 0x0001); break; // DBGE - Greater or Equal
                                    case 0xC: shouldBranch = (uae60_regs.sr & 0x8000) == (uae60_regs.sr & 0x0001); break; // DBLT - Less Than
                                    case 0xD: shouldBranch = (uae60_regs.sr & 0x8000) != 0; break; // DBGT - Greater Than
                                    case 0xE: shouldBranch = (uae60_regs.sr & 0x8000) == 0; break; // DBLE - Less or Equal
                                    case 0xF: shouldBranch = (uae60_regs.sr & 0x04) != 0; break;  // DBNE - Not Equal
                                    case 0x2: shouldBranch = (uae60_regs.sr & 0x08) == 0; break;  // DBMI - Minus
                                    case 0x3: shouldBranch = (uae60_regs.sr & 0x08) != 0; break;  // DBPL - Plus
                                }
                                if (shouldBranch || uae60_regs.d[data_reg] != -1) {
                                    uae60_regs.pc += displacement;
                                }
                            }
                            break;
                    } // switch (opcode & 0xF000)
                }
                break; // case 0x5

            case 0x6: // Grupo 6: Bcc, BSR
                {
                    // Calcula el desplazamiento
                    int16_t displacement = (int16_t)(opcode & 0xFF);
                    if (displacement == 0) {
                        displacement = (int16_t)get_next_word(uae60_regs.pc);
                        uae60_regs.pc += 2;
                    }

                    // Obtén la condición del salto
                    uint8_t condition = (opcode >> 8) & 0xF;

                    // Comprueba la condición
                    bool shouldBranch = false;
                    switch (condition) {
                        case 0x0: shouldBranch = true; break;  // BRA - Siempre salta
                        case 0x1: shouldBranch = false; break; // BSR - No se usa para la condición, se maneja por separado
                        case 0x2: shouldBranch = (uae60_regs.sr & 0x8000) == 0; break; // BHI
                        case 0x3: shouldBranch = (uae60_regs.sr & 0x8000) != 0 || (uae60_regs.sr & 0x4000) == 0; break; // BLS
                        case 0x4: shouldBranch = (uae60_regs.sr & 0x0001) == 0; break;  // CC - Carry Clear
                        case 0x5: shouldBranch = (uae60_regs.sr & 0x0001) != 0; break;  // CS - Carry Set
                        case 0x6: shouldBranch = (uae60_regs.sr & 0x04) != 0; break;  // EQ - Equal
                        case 0x7: shouldBranch = (uae60_regs.sr & 0x02) != 0; break;  // VS - Overflow Set
                        case 0x8: shouldBranch = (uae60_regs.sr & 0x02) == 0; break;  // VC - Overflow Clear
                        case 0x9: shouldBranch = (uae60_regs.sr & 0x8000) == 0 && (uae60_regs.sr & 0x4000) != 0; break; // HI - Higher
                        case 0xA: shouldBranch = (uae60_regs.sr & 0x8000) != 0 || (uae60_regs.sr & 0x4000) == 0; break; // LS - Lower or Same
                        case 0xB: shouldBranch = (uae60_regs.sr & 0x8000) == (uae60_regs.sr & 0x0001); break; // GE - Greater or Equal
                        case 0xC: shouldBranch = (uae60_regs.sr & 0x8000) != (uae60_regs.sr & 0x0001); break; // LT - Less Than
                        case 0xD: shouldBranch = (uae60_regs.sr & 0x8000) == 0; break; // GT - Greater Than
                        case 0xE: shouldBranch = (uae60_regs.sr & 0x8000) != 0; break; // LE - Less or Equal
                        case 0xF: shouldBranch = (uae60_regs.sr & 0x04) == 0; break;  // NE - Not Equal
                    }

                    // Realiza el salto si se cumple la condición
                    if (shouldBranch) {
                        uae60_regs.pc += displacement;
                    }

                    // Maneja BSR (salto a subrutina)
                    if (condition == 0x1) {
                        // Guarda la dirección de retorno en la pila
                        uae60_regs.a[7] -= 4;
                        *(uint32_t*)(amiga_memory + uae60_regs.a[7]) = uae60_regs.pc;

                        // Salta a la dirección de la subrutina
                        uae60_regs.pc += displacement;
                    }
                }
                break;

            case 0x8:  // Grupo 8: OR, DIVU, SBCD
                {
                    switch (opcode & 0xF1C0) {
                        case 0x8000: // OR.B
                            {
                                uint8_t src = (uint8_t)get_src_operand(opcode);
                                uint8_t dst = (uint8_t)get_dst_operand(opcode);
                                uint8_t result = dst | src;
                                uint32_t dst_addr = get_dst_operand(opcode);
                                amiga_memory[dst_addr] = result;
                                update_flags(result, 1);
                            }
                            break;
                        case 0x8040: // OR.W
                            {
                                uint16_t src = (uint16_t)get_src_operand(opcode);
                                uint16_t dst = (uint16_t)get_dst_operand(opcode);
                                uint16_t result = dst | src;
                                uint32_t dst_addr = get_dst_operand(opcode);
                                *(uint16_t*)(amiga_memory + dst_addr) = result;
                                update_flags(result, 2);
                            }
                            break;
                        case 0x8080: // OR.L
                            {
                                uint32_t src = get_src_operand(opcode);
                                uint32_t dst = get_dst_operand(opcode);
                                uint32_t result = dst | src;
                                uint32_t dst_addr = get_dst_operand(opcode);
                                *(uint32_t*)(amiga_memory + dst_addr) = result;
                                update_flags(result, 4);
                            }
                            break;
                        case 0x8100: // SBCD Dx,Dy
                            {
                                uint8_t src = (uint8_t)uae60_regs.d[opcode & 7];
                                uint8_t dst = (uint8_t)uae60_regs.d[(opcode >> 9) & 7];
                                bool borrow = (uae60_regs.sr & 0x0001) != 0;
                                uint8_t result = uae60_decimal_subtract(dst, src, borrow);
                                uae60_regs.d[(opcode >> 9) & 7] = (uae60_regs.d[(opcode >> 9) & 7] & 0xFFFFFF00) | result;
                                // Actualizar flags
                                uae60_regs.sr = (uae60_regs.sr & 0xFFFE) | (borrow_out ? 1 : 0);
                                update_flags(uae60_regs.d[(opcode >> 9) & 7], 1);
                            }
                            break;
                        case 0x8108: // SBCD -(Ax),-(Ay)
                            {
                                uae60_regs.a[(opcode >> 9) & 7] -= 1;
                                uae60_regs.a[opcode & 7] -= 1;
                                uint8_t src = amiga_memory[uae60_regs.a[opcode & 7]];
                                uint8_t dst = amiga_memory[uae60_regs.a[(opcode >> 9) & 7]];
                                bool borrow = (uae60_regs.sr & 0x0001) != 0;
                                uint8_t result = uae60_decimal_subtract(dst, src, borrow);
                                amiga_memory[uae60_regs.a[(opcode >> 9) & 7]] = result;
                                // Actualizar flags
                                uae60_regs.sr = (uae60_regs.sr & 0xFFFE) | (borrow_out ? 1 : 0);
         update_flags(uae60_regs.d[(opcode >> 9) & 7], 1);
                            }
                            break;
                        case 0x80C0: // DIVU.W
                            {
                                uint32_t src = get_src_operand(opcode);
                                uint16_t dst = uae60_regs.d[(opcode >> 9) & 7];
                                if (src == 0) {
                                    uae60_trap(5); // Exception: Divide by Zero
                                    return;
                                }
                                uint16_t quotient = dst / src;
                                uint16_t remainder = dst % src;
                                uae60_regs.d[(opcode >> 9) & 7] = (remainder << 16) | quotient;
                                update_flags((dst << 16) | quotient, 2);
                            }
                            break; // CORTE
                        case                       0x82C0: // DIVU.L
                            {
                                uint32_t src = get_src_operand(opcode);
                                uint64_t dst = ((uint64_t)uae60_regs.d[(opcode >> 9) & 7] << 32) | (uae60_regs.d[((opcode >> 9) & 7) + 1]);
                                if (src == 0) {
                                    uae60_trap(5); // Exception: Divide by Zero
                                    return;
                                }
                                uint32_t quotient = dst / src;
                                uint32_t remainder = dst % src;
                                uae60_regs.d[(opcode >> 9) & 7] = remainder;
                                uae60_regs.d[((opcode >> 9) & 7) + 1] = quotient;
                                update_flags(remainder, 4); // Flags se actualizan con el resto (remainder)
                            }
                            break;
                    } // switch (opcode & 0xF1C0)
                }
                break; // case 0x8

            case 0x9:  // Grupo 9: SUB, SUBX
                {
                    switch (opcode & 0xF1C0) {
                        case 0x9000: // SUB.B
                            {
                                uint8_t src = (uint8_t)get_src_operand(opcode);
                                uint8_t dst = (uint8_t)get_dst_operand(opcode);
                                uint8_t result = dst - src;
                                uint32_t dst_addr = get_dst_operand(opcode);
                                amiga_memory[dst_addr] = result;
                                update_flags(result, 1);
                            }
                            break;
                        case 0x9040: // SUB.W
                            {
                                uint16_t src = (uint16_t)get_src_operand(opcode);
                                uint16_t dst = (uint16_t)get_dst_operand(opcode);
                                uint16_t result = dst - src;
                                uint32_t dst_addr = get_dst_operand(opcode);
                                *(uint16_t*)(amiga_memory + dst_addr) = result;
                                update_flags(result, 2);
                            }
                            break;
                        case 0x9080: // SUB.L
                            {
                                uint32_t src = get_src_operand(opcode);
                                uint32_t dst = get_dst_operand(opcode);
                                uint32_t result = dst - src;
                                uint32_t dst_addr = get_dst_operand(opcode);
                                *(uint32_t*)(amiga_memory + dst_addr) = result;
                                update_flags(result, 4);
                            }
                            break;
                        case 0x90C0: // SUBA.W
                            {
                                uint16_t src = (uint16_t)get_src_operand(opcode);
                                uint8_t dst_reg = (opcode >> 9) & 7;
                                uae60_regs.a[dst_reg] -= src;
                            }
                            break;
                        case 0x91C0: // SUBA.L
                            {
                                uint32_t src = get_src_operand(opcode);
                                uint8_t dst_reg = (opcode >> 9) & 7;
                                uae60_regs.a[dst_reg] -= src;
                            }
                            break;
                        case 0x0400: // SUBI.B
                            {
                                uint8_t src = (uint8_t)get_src_operand(opcode);
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint8_t result = amiga_memory[dst_addr] - src;
                                amiga_memory[dst_addr] = result;
                                update_flags(result, 1);
                            }
                            break;
                        case 0x0440: // SUBI.W
                            {
                                uint16_t src = (uint16_t)get_src_operand(opcode);
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint16_t result = *(uint16_t*)(amiga_memory + dst_addr) - src;
                                *(uint16_t*)(amiga_memory + dst_addr) = result;
                                update_flags(result, 2);
                            }
                            break;
                        case 0x0480: // SUBI.L
                            {
                                uint32_t src = get_src_operand(opcode);
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint32_t result = *(uint32_t*)(amiga_memory + dst_addr) - src;
                                *(uint32_t*)(amiga_memory + dst_addr) = result;
                                update_flags(result, 4);
                            }
                            break;
                        case 0x0100: // SUBX.B
                            {
                                uint8_t src = (uint8_t)uae60_regs.d[opcode & 7];
                                uint8_t dst = (uint8_t)uae60_regs.d[(opcode >> 9) & 7];
                                bool borrow = (uae60_regs.sr & 0x0001) != 0;
                                uint8_t result = uae60_decimal_subtract(dst, src, borrow);
                                uae60_regs.d[(opcode >> 9) & 7] = (uae60_regs.d[(opcode >> 9) & 7] & 0xFFFFFF00) | result;
                                // Actualizar flags
                                uae60_regs.sr = (uae60_regs.sr & 0xFFFE) | (borrow_out ? 1 : 0);
                                update_flags(uae60_regs.d[(opcode >> 9) & 7], 1);
                            }
                            break;
                        case 0x0108: // SUBX.W
                            {
                                uae60_regs.a[(opcode >> 9) & 7] -= 2;
                                uae60_regs.a[opcode & 7] -= 2;
                                uint16_t src = *(uint16_t*)(amiga_memory + uae60_regs.a[opcode & 7]);
                                uint16_t dst = *(uint16_t*)(amiga_memory + uae60_regs.a[(opcode >> 9) & 7]);
                                bool borrow = (uae60_regs.sr & 0x0001) != 0;
                                uint16_t result = uae60_decimal_subtract(dst, src, borrow);
                                *(uint16_t*)(amiga_memory + uae60_regs.a[(opcode >> 9) & 7]) = result;
                                // Actualizar flags
                                uae60_regs.sr = (uae60_regs.sr & 0xFFFE) | (borrow_out ? 1 : 0);
                                update_flags(memory[uae60_regs.a[(opcode >> 9) & 7]], 2);
                            }
                            break;
                        case 0x0110: // SUBX.L
                            {
                                uae60_regs.a[(opcode >> 9) & 7] -= 4;
                                uae60_regs.a[opcode & 7] -= 4;
                                uint32_t src = *(uint32_t*)(amiga_memory + uae60_regs.a[opcode & 7]);
                                uint32_t dst = *(uint32_t*)(amiga_memory + uae60_regs.a[(opcode >> 9) & 7]);
                                bool borrow = (uae60_regs.sr & 0x0001) != 0;
                                uint32_t result = uae60_decimal_subtract(dst, src, borrow);
                                *(uint32_t*)(amiga_memory + uae60_regs.a[(opcode >> 9) & 7]) = result;
                                // Actualizar flags
                                uae60_regs.sr = (uae60_regs.sr & 0xFFFE) | (borrow_out ? 1 : 0);
                                update_flags(memory[uae60_regs.a[(opcode >> 9) & 7]], 4);
                            }
                            break;
                    } // switch (opcode & 0xF1C0)
                }
                break; // case 0x9
            case 0xA:  // Grupo A: Instrucciones Varias
                {
                    switch (opcode & 0xF0C0) {
                        case 0xA000: // BTST
                            {
                                uint32_t bitnum = get_src_operand(opcode) & 31; // Asegura que el número de bit esté entre 0 y 31
                                uint32_t src = get_dst_operand(opcode);
                                uae60_regs.sr &= ~(1 << 6); // Borra el flag Zero
                                if ((src & (1 << bitnum)) == 0) {
                                    uae60_regs.sr |= (1 << 6); // Establece el flag Zero si el bit está en 0
                                }
                            }
                            break;
                        case 0xA040: // BCHG
                            {
                                uint32_t bitnum = get_src_operand(opcode) & 31; // Asegura que el número de bit esté entre 0 y 31
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint32_t dst = uae60_mem_read(dst_addr, 4); // Lee el valor de destino de la memoria
                                uint32_t original_bit = (dst >> bitnum) & 1; // Obtiene el valor original del bit
                                dst ^= (1 << bitnum); // Invierte el bit
                                uae60_mem_write(dst_addr, 4, dst); // Escribe el valor modificado en la memoria
                                uae60_regs.sr &= ~(1 << 6); // Borra el flag Zero
                                if (original_bit == 0) {
                                    uae60_regs.sr |= (1 << 6); // Establece el flag Zero si el bit original estaba en 0
                                }
                            }
                            break;
                        case 0xA080: // BCLR
                            {
                                uint32_t bitnum = get_src_operand(opcode) & 31; // Asegura que el número de bit esté entre 0 y 31
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint32_t dst = uae60_mem_read(dst_addr, 4); // Lee el valor de destino de la memoria
                                uint32_t original_bit = (dst >> bitnum) & 1; // Obtiene el valor original del bit
                                dst &= ~(1 << bitnum); // Borra el bit
                                uae60_mem_write(dst_addr, 4, dst); // Escribe el valor modificado en la memoria
                                uae60_regs.sr &= ~(1 << 6); // Borra el flag Zero
                                if (original_bit == 0) {
                                    uae60_regs.sr |= (1 << 6); // Establece el flag Zero si el bit original estaba en 0
                                }
                            }
                            break;
                        case 0xA0C0: // BSET
                            {
                                uint32_t bitnum = get_src_operand(opcode) & 31; // Asegura que el número de bit esté entre 0 y 31
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint32_t dst = uae60_mem_read(dst_addr, 4); // Lee el valor de destino de la memoria
                                uint32_t original_bit = (dst >> bitnum) & 1; // Obtiene el valor original del bit
                                dst |= (1 << bitnum); // Establece el bit
                                uae60_mem_write(dst_addr, 4, dst); // Escribe el valor modificado en la memoria
                                uae60_regs.sr &= ~(1 << 6); // Borra el flag Zero
                                if (original_bit == 0) {
                                    uae60_regs.sr |= (1 << 6); // Establece el flag Zero si el bit original estaba en 0
                                }
                            }
                            break;
                    }
                }
                break; // case 0xA CORTE
           case 0xB:  // Grupo B: CMP, EOR
                {
                    switch (opcode & 0xF1C0) {
                        case 0xB000: // CMP.B
                            {
                                uint8_t src = (uint8_t)get_src_operand(opcode);
                                uint8_t dst = (uint8_t)get_dst_operand(opcode);
                                update_flags(dst - src, 1);
                            }
                            break;
                        case 0xB040: // CMP.W
                            {
                                uint16_t src = (uint16_t)get_src_operand(opcode);
                                uint16_t dst = (uint16_t)get_dst_operand(opcode);
                                update_flags(dst - src, 2);
                            }
                            break;
                        case 0xB080: // CMP.L
                            {
                                uint32_t src = get_src_operand(opcode);
                                uint32_t dst = get_dst_operand(opcode);
                                update_flags(dst - src, 4);
                            }
                            break;
                        case 0xB0C0: // CMPA.W
                            {
                                uint16_t src = (uint16_t)get_src_operand(opcode);
                                uint8_t dst_reg = (opcode >> 9) & 7;
                                update_flags(uae60_regs.a[dst_reg] - src, 2);
                            }
                            break;
                        case 0xB1C0: // CMPA.L
                            {
                                uint32_t src = get_src_operand(opcode);
                                uint8_t dst_reg = (opcode >> 9) & 7;
                                update_flags(uae60_regs.a[dst_reg] - src, 4);
                            }
                            break;
                        case 0xB100: // EOR.B
                            {
                                uint8_t src = (uint8_t)get_src_operand(opcode);
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint8_t dst = amiga_memory[dst_addr];
                                uint8_t result = dst ^ src;
                                amiga_memory[dst_addr] = result;
                                update_flags(result, 1);
                            }
                            break;
                        case 0xB140: // EOR.W
                            {
                                uint16_t src = (uint16_t)get_src_operand(opcode);
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint16_t dst = *(uint16_t*)(amiga_memory + dst_addr);
                                uint16_t result = dst ^ src;
                                *(uint16_t*)(amiga_memory + dst_addr) = result;
                                update_flags(result, 2);
                            }
                            break;
                        case 0xB180: // EOR.L
                            {
                                uint32_t src = get_src_operand(opcode);
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint32_t dst = *(uint32_t*)(amiga_memory + dst_addr);
                                uint32_t result = dst ^ src;
                                *(uint32_t*)(amiga_memory + dst_addr) = result;
                                update_flags(result, 4);
                            }
                            break;
                    } // switch (opcode & 0xF1C0)
                }
                break; // case 0xB

            case 0xC:  // Grupo C: AND, MULU, ABCD
                {
                    switch (opcode & 0xF1C0) {
                        case 0xC000: // AND.B
                            {
                                uint8_t src = (uint8_t)get_src_operand(opcode);
                                uint8_t dst = (uint8_t)get_dst_operand(opcode);
                                uint8_t result = dst & src;
                                uint32_t dst_addr = get_dst_operand(opcode);
                                amiga_memory[dst_addr] = result;
                                update_flags(result, 1);
                            }
                            break;
                        case 0xC040: // AND.W
                            {
                                uint16_t src = (uint16_t)get_src_operand(opcode);
                                uint16_t dst = (uint16_t)get_dst_operand(opcode);
                                uint16_t result = dst & src;
                                uint32_t dst_addr = get_dst_operand(opcode);
                                *(uint16_t*)(amiga_memory + dst_addr) = result;
                                update_flags(result, 2);
                            }
                            break;
                        case 0xC080: // AND.L
                            {
                                uint32_t src = get_src_operand(opcode);
                                uint32_t dst = get_dst_operand(opcode);
                                uint32_t result = dst & src;
                                uint32_t dst_addr = get_dst_operand(opcode);
                                *(uint32_t*)(amiga_memory + dst_addr) = result;
                                update_flags(result, 4);
                            }
                            break;
                        case 0xC0C0: // MULU.W
                            {
                                uint16_t src = (uint16_t)get_src_operand(opcode);
                                uint16_t dst = (uint16_t)uae60_regs.d[(opcode >> 9) & 7];
                                uint32_t result = (uint32_t)dst * (uint32_t)src;
                                uae60_regs.d[(opcode >> 9) & 7] = result;
                                update_flags(result, 4);
                            }
                            break;
                        case 0xC1C0: // MULS.W
                            {
                                int16_t src = (int16_t)get_src_operand(opcode);
                                int16_t dst = (int16_t)uae60_regs.d[(opcode >> 9) & 7];
                                int32_t result = (int32_t)dst * (int32_t)src;
                                uae60_regs.d[(opcode >> 9) & 7] = result;
                                update_flags(result, 4);
                            }
                            break;
                        case 0xC100: // ABCD Dx,Dy
                            {
                                uint8_t src = (uint8_t)uae60_regs.d[opcode & 7];
                                uint8_t dst = (uint8_t)uae60_regs.d[(opcode >> 9) & 7];
                                bool carry = (uae60_regs.sr & 0x0001) != 0;
                                uint8_t result = uae60_decimal_add(dst, src, carry);
                                uae60_regs.d[(opcode >> 9) & 7] = (uae60_regs.d[(opcode >> 9) & 7] & 0xFFFFFF00) | result;
                                // Actualizar flags
                                uae60_regs.sr = (uae60_regs.sr & 0xFFFE) | (carry_out ? 1 : 0);
                                update_flags(uae60_regs.d[(opcode >> 9) & 7], 1);
                            }
                            break;
                        case 0xC108: // ABCD -(Ax),-(Ay)
                            {
                                uae60_regs.a[(opcode >> 9) & 7] -= 1;
                                uae60_regs.a[opcode & 7] -= 1;
                                uint8_t src = amiga_memory[uae60_regs.a[opcode & 7]];
                                uint8_t dst = amiga_memory[uae60_regs.a[(opcode >> 9) & 7]];
                                bool carry = (uae60_regs.sr & 0x0001) != 0;
                                uint8_t result = uae60_decimal_add(dst, src, carry);
                                amiga_memory[uae60_regs.a[(opcode >> 9) & 7]] = result;
                                // Actualizar flags
                                uae60_regs.sr = (uae60_regs.sr & 0xFFFE) | (carry_out ? 1 : 0);
                                update_flags(memory[uae60_regs.a[(opcode >> 9) & 7]], 1);
                            }
                            break;
                    } // switch (opcode & 0xF1C0)
                }
                break; // case 0xC

            case 0xD:  // Grupo D: ADD, ADDX
                {
                    switch (opcode & 0xF1C0) {
                        case 0xD000: // ADD.B
                            {
                                uint8_t src = (uint8_t)get_src_operand(opcode);
                                uint8_t dst = (uint8_t)get_dst_operand(opcode);
                                uint8_t result = dst + src;
                                uint32_t dst_addr = get_dst_operand(opcode);
                                amiga_memory[dst_addr] = result;
                                update_flags(result, 1);
                            }
                            break;
                        case 0xD040: // ADD.W
                            {
                                uint16_t src = (uint16_t)get_src_operand(opcode);
                                uint16_t dst = (uint16_t)get_dst_operand(opcode);
                                uint16_t result = dst + src;
                                uint32_t dst_addr = get_dst_operand(opcode);
                                *(uint16_t*)(amiga_memory + dst_addr) = result;
                                update_flags(result, 2);
                            }
                            break;
                        case 0xD080: // ADD.L
                            {
                                uint32_t src = get_src_operand(opcode);
                                uint32_t dst = get_dst_operand(opcode);
                                uint32_t result = dst + src;
                                uint32_t dst_addr = get_dst_operand(opcode);
                                *(uint32_t*)(amiga_memory + dst_addr) = result;
                                update_flags(result, 4);
                            }
                            break;
                        case 0xD0C0: // ADDA.W
                            {
                                uint16_t src = (uint16_t)get_src_operand(opcode);
                                uint8_t dst_reg = (opcode >> 9) & 7;
                                uae60_regs.a[dst_reg] += src;
                            }
                            break;
                        case 0xD1C0: // ADDA.L
                            {
                                uint32_t src = get_src_operand(opcode);
                                uint8_t dst_reg = (opcode >> 9) & 7;
                                uae60_regs.a[dst_reg] += src;
                            }
                            break;
                        case 0x0600: // ADDI.B
                            {
                                uint8_t src = (uint8_t)get_src_operand(opcode);
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint8_t result = amiga_memory[dst_addr] + src;
                                amiga_memory[dst_addr] = result;
                                update_flags(result, 1);
                            }
                            break;
                        case 0x0640: // ADDI.W
                            {
                                uint16_t src = (uint16_t)get_src_operand(opcode);
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint16_t result = *(uint16_t*)(amiga_memory + dst_addr) + src;
                                *(uint16_t*)(amiga_memory + dst_addr) = result;
                                update_flags(result, 2);
                            }
                            break;
                        case 0x0680: // ADDI.L
                            {
                                uint32_t src = get_src_operand(opcode);
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint32_t result = *(uint32_t*)(amiga_memory + dst_addr) + src;
                                *(uint32_t*)(amiga_memory + dst_addr) = result;
                                update_flags(result, 4);
                            }
                            break;
                        case 0x0900: // ADDX.B
                            {
                                uint8_t src = (uint8_t)uae60_regs.d[opcode & 7];
                                uint8_t dst = (uint8_t)uae60_regs.d[(opcode >> 9) & 7];
                                bool carry = (uae60_regs.sr & 0x0001) != 0;
                                uint8_t result = uae60_decimal_add(dst, src, carry);
                                uae60_regs.d[(opcode >> 9) & 7] = (uae60_regs.d[(opcode >> 9) & 7] & 0xFFFFFF00) | result;
                                // Actualizar flags
uae60_regs.sr = (uae60_regs.sr & 0xFFFE) | (carry_out ? 1 : 0);
update_flags(uae60_regs.d[(opcode >> 9) & 7], 1);
                            }
                            break;
                        case 0x0908: // ADDX.W
                            {
                                uae60_regs.a[(opcode >> 9) & 7] -= 2;
                                uae60_regs.a[opcode & 7] -= 2;
                                uint16_t src = *(uint16_t*)(amiga_memory + uae60_regs.a[opcode & 7]);
                                uint16_t dst = *(uint16_t*)(amiga_memory + uae60_regs.a[(opcode >> 9) & 7]);
                                bool carry = (uae60_regs.sr & 0x0001) != 0;
                                uint16_t result = uae60_decimal_add(dst, src, carry);
                                *(uint16_t*)(amiga_memory + uae60_regs.a[(opcode >> 9) & 7]) = result;
                                // Actualizar flags
uae60_regs.sr = (uae60_regs.sr & 0xFFFE) | (carry_out ? 1 : 0);
update_flags(memory[uae60_regs.a[(opcode >> 9) & 7]], 2);

                            }
                            break;
                        case 0x0910: // ADDX.L
                            {
                                uae60_regs.a[(opcode >> 9) & 7] -= 4;
                                uae60_regs.a[opcode & 7] -= 4;
                                uint32_t src = *(uint32_t*)(amiga_memory + uae60_regs.a[opcode & 7]);
                                uint32_t dst = *(uint32_t*)(amiga_memory + uae60_regs.a[(opcode >> 9) & 7]);
                                bool carry = (uae60_regs.sr & 0x0001) != 0;
                                uint32_t result = uae60_decimal_add(dst, src, carry);
                                *(uint32_t*)(amiga_memory + uae60_regs.a[(opcode >> 9) & 7]) = result;
                                // Actualizar flags
uae60_regs.sr = (uae60_regs.sr & 0xFFFE) | (carry_out ? 1 : 0);
update_flags(memory[uae60_regs.a[(opcode >> 9) & 7]], 4);
                            }
                            break;
                    } // switch (opcode & 0xF1C0)
                }
                break; // case 0xD

            case 0xE:  // Grupo E: ASL, ASR
                {
                    switch (opcode & 0xF1C0) {
                        case 0xE000: // ASR.B
                            {
                                uint8_t count = (uint8_t)get_src_operand(opcode);
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint8_t data = amiga_memory[dst_addr];
                                uint8_t result = (int8_t)data >> count; // Desplazamiento aritmético
                                amiga_memory[dst_addr] = result;
                                update_flags(result, 1);
                                // Actualizar el Carry Flag (CF) con el último bit desplazado
                                uae60_regs.sr = (uae60_regs.sr & 0xFFFE) | ((data >> (count - 1)) & 1);
                            }
                            break;
                        case 0xE040: // ASR.W
                            {
                                uint8_t count = (uint8_t)get_src_operand(opcode);
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint16_t data = *(uint16_t*)(amiga_memory + dst_addr);
                                uint16_t result = (int16_t)data >> count; // Desplazamiento aritmético
                                *(uint16_t*)(amiga_memory + dst_addr) = result;
                                update_flags(result, 2);
                                // Actualizar el Carry Flag (CF) con el último bit desplazado
                                uae60_regs.sr = (uae60_regs.sr & 0xFFFE) | ((data >> (count - 1)) & 1);
                            }
                            break;
                        case 0xE080: // ASR.L
                            {
                                uint8_t count = (uint8_t)get_src_operand(opcode);
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint32_t data = *(uint32_t*)(amiga_memory + dst_addr);
                                uint32_t result = (int32_t)data >> count; // Desplazamiento aritmético
                                *(uint32_t*)(amiga_memory + dst_addr) = result;
                                update_flags(result, 4);
                                // Actualizar el Carry Flag (CF) con el último bit desplazado
                                uae60_regs.sr = (uae60_regs.sr & 0xFFFE) | ((data >> (count - 1)) & 1);
                            }
                            break;
                        case 0xE100: // ASL.B
                            {
                                uint8_t count = (uint8_t)get_src_operand(opcode);
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint8_t data = amiga_memory[dst_addr];
                                uint8_t result = data << count;
                                amiga_memory[dst_addr] = result;
                                update_flags(result, 1);
                                // Actualizar el Carry Flag (CF) con el último bit desplazado
			update_flags(result, 1);
                                uae60_regs.sr = (uae60_regs.sr & 0xFFFE) | ((data >> (8 - count)) & 1);
                            }
                            break;
                        case 0xE140: // ASL.W
                            {
                                uint8_t count = (uint8_t)get_src_operand(opcode);
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint16_t data = *(uint16_t*)(amiga_memory + dst_addr);
                                uint16_t result = data << count;
                                *(uint16_t*)(amiga_memory + dst_addr) = result;
                                update_flags(result, 2);
                                // Actualizar el Carry Flag (CF) con el último bit desplazado
			update_flags(result, 2);
                                uae60_regs.sr = (uae60_regs.sr & 0xFFFE) | ((data >> (16 - count)) & 1);
                            }
                            break;
                        case 0xE180: // ASL.L
                            {
                                uint8_t count = (uint8_t)get_src_operand(opcode);
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint32_t data = *(uint32_t*)(amiga_memory + dst_addr);
                                uint32_t result = data << count;
                                *(uint32_t*)(amiga_memory + dst_addr) = result;
                                update_flags(result, 4);
                                // Actualizar el Carry Flag (CF) con el último bit desplazado
			update_flags(result, 4);
                                uae60_regs.sr = (uae60_regs.sr & 0xFFFE) | ((data >> (32 - count)) & 1);
                            }
                            break;
                        case 0xE008: // LSR.B
                            {
                                uint8_t count = (uint8_t)get_src_operand(opcode);
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint8_t data = amiga_memory[dst_addr];
                                uint8_t result = data >> count; // Desplazamiento lógico
                                amiga_memory[dst_addr] = result;
                                update_flags(result, 1);
                                // Actualizar el Carry Flag (CF) con el último bit desplazado
                                uae60_regs.sr = (uae60_regs.sr & 0xFFFE) | ((data >> (count - 1)) & 1);
                            }
                            break;
                        case 0xE048: // LSR.W
                            {
                                uint8_t count = (uint8_t)get_src_operand(opcode);
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint16_t data = *(uint16_t*)(amiga_memory + dst_addr);
                                uint16_t result = data >> count; // Desplazamiento lógico
                                *(uint16_t*)(amiga_memory + dst_addr) = result;
                                update_flags(result, 2);
                                // Actualizar el Carry Flag (CF) con el último bit desplazado
                                uae60_regs.sr = (uae60_regs.sr & 0xFFFE) | ((data >> (count - 1)) & 1);
                            }
                            break;
                        case 0xE088: // LSR.L
                            {
                                uint8_t count = (uint8_t)get_src_operand(opcode);
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint32_t data = *(uint32_t*)(amiga_memory + dst_addr);
                                uint32_t result = data >> count; // Desplazamiento lógico
                                *(uint32_t*)(amiga_memory + dst_addr) = result;
                                update_flags(result, 4);
                                // Actualizar el Carry Flag (CF) con el último bit desplazado
                                uae60_regs.sr = (uae60_regs.sr & 0xFFFE) | ((data >> (count - 1)) & 1);
                            }
                            break;
                        case 0xE108: // LSL.B
                            {
                                uint8_t count = (uint8_t)get_src_operand(opcode);
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint8_t data = amiga_memory[dst_addr];
                                uint8_t result = data << count;
                                amiga_memory[dst_addr] = result;
                                update_flags(result, 1);
                                // Actualizar el Carry Flag (CF) con el último bit desplazado
                                uae60_regs.sr = (uae60_regs.sr & 0xFFFE) | ((data >> (8 - count)) & 1);
                            }
                            break;
                        case 0xE148: // LSL.W
                            {
                                uint8_t count = (uint8_t)get_src_operand(opcode);
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint16_t data = *(uint16_t*)(amiga_memory + dst_addr);
                                uint16_t result = data << count;
                                *(uint16_t*)(amiga_memory + dst_addr) = result;
                                update_flags(result, 2);
                                // Actualizar el Carry Flag (CF) con el último bit desplazado
                                uae60_regs.sr = (uae60_regs.sr & 0xFFFE) | ((data >> (16 - count)) & 1);
                            }
                            break;
                        case 0xE188: // LSL.L
                            {
                                uint8_t count = (uint8_t)get_src_operand(opcode);
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint32_t data = *(uint32_t*)(amiga_memory + dst_addr);
                                uint32_t result = data << count;
                                *(uint32_t*)(amiga_memory + dst_addr) = result;
                                update_flags(result, 4);
                                // Actualizar el Carry Flag (CF) con el último bit desplazado
                                uae60_regs.sr = (uae60_regs.sr & 0xFFFE) | ((data >> (32 - count)) & 1);
                            }
                            break;
                        case 0xE00C: // ROXR.B
                            {
                                uint8_t count = (uint8_t)get_src_operand(opcode);
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint8_t data = amiga_memory[dst_addr];
                                uint8_t result = (data >> count) | (data << (8 - count)); // Rotación con extensión
                                amiga_memory[dst_addr] = result;
                                update_flags(result, 1);
                                // Actualizar el Carry Flag (CF) con el último bit desplazado
                                uae60_regs.sr = (uae60_regs.sr & 0xFFFE) | ((data >> (count - 1)) & 1);
                            }
                            break;
                        case 0xE04C: // ROXR.W
                            {
                                uint8_t count = (uint8_t)get_src_operand(opcode);
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint16_t data = *(uint16_t*)(amiga_memory + dst_addr);
                                uint16_t result = (data >> count) | (data << (16 - count)); // Rotación con extensión
                                *(uint16_t*)(amiga_memory + dst_addr) = result;
                                update_flags(result, 2);
                                // Actualizar el Carry Flag (CF) con el último bit desplazado
                                uae60_regs.sr = (uae60_regs.sr & 0xFFFE) | ((data >> (count - 1)) & 1);
                            }
                            break;
                        case 0xE08C: // ROXR.L
                            {
                                uint8_t count = (uint8_t)get_src_operand(opcode);
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint32_t data = *(uint32_t*)(amiga_memory + dst_addr);
                                uint32_t result = (data >> count) | (data << (32 - count)); // Rotación con extensión
                                *(uint32_t*)(amiga_memory + dst_addr) = result;
                                update_flags(result, 4);
                                // Actualizar el Carry Flag (CF) con el último bit desplazado
                                uae60_regs.sr = (uae60_regs.sr & 0xFFFE) | ((data >> (count - 1)) & 1);
                            }
                            break;
                        case 0xE10C: // ROXL.B
                            {
                                uint8_t count = (uint8_t)get_src_operand(opcode);
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint8_t data = amiga_memory[dst_addr];
                                uint8_t result = (data << count) | (data >> (8 - count)); // Rotación con extensión
                                amiga_memory[dst_addr] = result;
                                update_flags(result, 1);
                                // Actualizar el Carry Flag (CF) con el último bit desplazado
                                uae60_regs.sr = (uae60_regs.sr & 0xFFFE) | ((result) & 1);
                            }
                            break;
                        case 0xE14C: // ROXL.W
                            {
                                uint8_t count = (uint8_t)get_src_operand(opcode);
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint16_t data = *(uint16_t*)(amiga_memory + dst_addr);
                                uint16_t result = (data << count) | (data >> (16 - count)); // Rotación con extensión
                                *(uint16_t*)(amiga_memory + dst_addr) = result;
                                update_flags(result, 2);
                                // Actualizar el Carry Flag (CF) con el último bit desplazado
                                uae60_regs.sr = (uae60_regs.sr & 0xFFFE) | ((result >> 15) & 1);
                            }
                            break;
                        case 0xE18C: // ROXL.L
                            {
                                uint8_t count = (uint8_t)get_src_operand(opcode);
                                uint32_t dst_addr = get_dst_operand(opcode);
                                uint32_t data = *(uint32_t*)(amiga_memory + dst_addr);
                                uint32_t result = (data << count) | (data >> (32 - count)); // Rotación con extensión
                                *(uint32_t*)(amiga_memory + dst_addr) = result;
                                update_flags(result, 4);
                                // Actualizar el Carry Flag (CF) con el último bit desplazado
                                uae60_regs.sr = (uae60_regs.sr & 0xFFFE) | ((result >> 31) & 1);
                            }
                            break;
                    } // switch (opcode & 0xF1C0)
                }
                break; // case 0xE

            case 0xF:  // Grupo F: Instrucciones de Coma Flotante
                {
                    // Actualizar last_fpu_opcode si es una instrucción FPU
                    last_fpu_opcode = opcode;

                    switch (opcode & 0xF1C0) {
                        case 0xF000: // FADD
                            {
                                // Obtener los operandos de la FPU
                                double src = get_fp_operand(opcode);
                                double dst = uae60_regs.fp[(opcode >> 9) & 7];

                                // Realizar la suma
                                double result = dst + src;

                                // Almacenar el resultado en el registro de la FPU
                                uae60_regs.fp[(opcode >> 9) & 7] = result;

                                // Actualizar los flags de la FPU (FPSR)
                                update_fpu_flags();
                            }
                            break;
                        case 0xF040: // FSUB
                            {
                                // Obtener los operandos de la FPU
                                double src = get_fp_operand(opcode);
                                double dst = uae60_regs.fp[(opcode >> 9) & 7];

                                // Realizar la resta
                                double result = dst - src;

                                // Almacenar el resultado en el registro de la FPU
                                uae60_regs.fp[(opcode >> 9) & 7] = result;

                                // Actualizar los flags de la FPU (FPSR)
                                update_fpu_flags();
                            }
                            break;
                        case 0xF080: // FMUL
                            {
                                // Obtener los operandos de la FPU
                                double src = get_fp_operand(opcode);
                                double dst = uae60_regs.fp[(opcode >> 9) & 7];

                                // Realizar la multiplicación
                                double result = dst * src;

                                // Almacenar el resultado en el registro de la FPU
                                uae60_regs.fp[(opcode >> 9) & 7] = result;

                                // Actualizar los flags de la FPU (FPSR)
                                update_fpu_flags();
                            }
                            break;
                        case 0xF0C0: // FDIV
                            {
                                // Obtener los operandos de la FPU
                                double src = get_fp_operand(opcode);
                                double dst = uae60_regs.fp[(opcode >> 9) & 7];

                                // Realizar la división
                                if (src == 0.0) {
                                    // Manejar la excepción de división por cero
                                    handle_fpu_exception(uae60_regs.fpsr & 0x0004); // DZ (Divide by Zero)
                                } else {
                                    double result = dst / src;

                                    // Almacenar el resultado en el registro de la FPU
                                    uae60_regs.fp[(opcode >> 9) & 7] = result;

                                    // Actualizar CORTE
                                  // los flags de la FPU (FPSR)
                                    update_fpu_flags();
                                }
                            }
                            break;
		}
                        case 0xF200: // FADD.S
                            {
                                float src_f = *(float*)(amiga_memory + get_src_operand(opcode));
                                float dst_f = get_fp_operand((opcode >> 9) & 7);
                                asm("flds %0" : : "m" (dst_f));
                                asm("fadds %0" : : "m" (src_f));
                                asm("fstps %0" : "=m" (dst_f));
                                uae60_regs.fp[(opcode >> 9) & 7] = set_fp_register(dst_f);
                                update_fpu_flags();
                            }
                            break;
                        case 0xF210: // FADD.D
                            {
                                double src_d = *(double*)(amiga_memory + get_src_operand(opcode));
                                double dst_d = get_fp_operand((opcode >> 9) & 7);
                                asm("fldl %0" : : "m" (dst_d));
                                asm("faddl %0" : : "m" (src_d));
                                asm("fstpl %0" : "=m" (dst_d));
                                uae60_regs.fp[(opcode >> 9) & 7] = set_fp_register(dst_d);
                                update_fpu_flags();
                            }
                            break;
                        case 0xF220: // FADD.X
                            {
                                long double src_x = *(long double*)(amiga_memory + get_src_operand(opcode));
                                long double dst_x = get_fp_operand((opcode >> 9) & 7);
                                asm("fldt %0" : : "m" (dst_x));
                                asm("faddt %0" : : "m" (src_x));
                                asm("fstpt %0" : "=m" (dst_x));
                                uae60_regs.fp[(opcode >> 9) & 7] = set_fp_register(dst_x);
                                update_fpu_flags();
                            }
                            break;
                        case 0xF202: // FSUB.S
                            {
                                float src_f = *(float*)(amiga_memory + get_src_operand(opcode));
                                float dst_f = get_fp_operand((opcode >> 9) & 7);
                                asm("flds %0" : : "m" (dst_f));
                                asm("fsubs %0" : : "m" (src_f));
                                asm("fstps %0" : "=m" (dst_f));
                                uae60_regs.fp[(opcode >> 9) & 7] = set_fp_register(dst_f);
                                update_fpu_flags();
                            }
                            break;
                        case 0xF212: // FSUB.D
                            {
                                double src_d = *(double*)(amiga_memory + get_src_operand(opcode));
                                double dst_d = get_fp_operand((opcode >> 9) & 7);
                                asm("fldl %0" : : "m" (dst_d));
                                asm("fsubl %0" : : "m" (src_d));
                                asm("fstpl %0" : "=m" (dst_d));
                                uae60_regs.fp[(opcode >> 9) & 7] = set_fp_register(dst_d);
                                update_fpu_flags();
                            }
                            break;
                        case 0xF222: // FSUB.X
                            {
                                long double src_x = *(long double*)(amiga_memory + get_src_operand(opcode));
                                long double dst_x = get_fp_operand((opcode >> 9) & 7);
                                asm("fldt %0" : : "m" (dst_x));
                                asm("fsubt %0" : : "m" (src_x));
                                asm("fstpt %0" : "=m" (dst_x));
                                uae60_regs.fp[(opcode >> 9) & 7] = set_fp_register(dst_x);
                                update_fpu_flags();
                            }
                            break;
                        case 0xF204: // FMUL.S
                            {
                                float src_f = *(float*)(amiga_memory + get_src_operand(opcode));
                                float dst_f = get_fp_operand((opcode >> 9) & 7);
                                asm("flds %0" : : "m" (dst_f));
                                asm("fmuls %0" : : "m" (src_f));
                                asm("fstps %0" : "=m" (dst_f));
                                uae60_regs.fp[(opcode >> 9) & 7] = set_fp_register(dst_f);
                                update_fpu_flags();
                            }
                            break;
                        case 0xF214: // FMUL.D
                            {
                                double src_d = *(double*)(amiga_memory + get_src_operand(opcode));
                                double dst_d = get_fp_operand((opcode >> 9) & 7);
                                asm("fldl %0" : : "m" (dst_d));
                                asm("fmull %0" : : "m" (src_d));
                                asm("fstpl %0" : "=m" (dst_d));
                                uae60_regs.fp[(opcode >> 9) & 7] = set_fp_register(dst_d);
                                update_fpu_flags();
                            }
                            break;
                        case 0xF224: // FMUL.X
                            {
                                long double src_x = *(long double*)(amiga_memory + get_src_operand(opcode));
                                long double dst_x = get_fp_operand((opcode >> 9) & 7);
                                asm("fldt %0" : : "m" (dst_x));
                                asm("fmult %0" : : "m" (src_x));
                                asm("fstpt %0" : "=m" (dst_x));
                                uae60_regs.fp[(opcode >> 9) & 7] = set_fp_register(dst_x);
                                update_fpu_flags();
                            }
                            break;
                        case 0xF206: // FDIV.S
                            {
                                float src_f = *(float*)(amiga_memory + get_src_operand(opcode));
                                float dst_f = get_fp_operand((opcode >> 9) & 7);
                                asm("flds %0" : : "m" (dst_f));
                                asm("fdivs %0" : : "m" (src_f));
                                asm("fstps %0" : "=m" (dst_f));
                                uae60_regs.fp[(opcode >> 9) & 7] = set_fp_register(dst_f);
                                update_fpu_flags();
                            }
                            break;
                        case 0xF216: // FDIV.D
                            {
                                double src_d = *(double*)(amiga_memory + get_src_operand(opcode));
                                double dst_d = get_fp_operand((opcode >> 9) & 7);
                                asm("fldl %0" : : "m" (dst_d));
                                asm("fdivl %0" : : "m" (src_d));
                                asm("fstpl %0" : "=m" (dst_d));
                                uae60_regs.fp[(opcode >> 9) & 7] = set_fp_register(dst_d);
                                update_fpu_flags();
                            }
                            break;
                        case 0xF226: // FDIV.X
                            {
                                long double src_x = *(long double*)(amiga_memory + get_src_operand(opcode));
                                long double dst_x = get_fp_operand((opcode >> 9) & 7);
                                asm("fldt %0" : : "m" (dst_x));
                                asm("fdivt %0" : : "m" (src_x));
                                asm("fstpt %0" : "=m" (dst_x));
                                uae60_regs.fp[(opcode >> 9) & 7] = set_fp_register(dst_x);
                                update_fpu_flags();
                            }
                            break;
                        case 0xF207: { // FSGLDIV
                            float src_f = *(float*)(amiga_memory + get_src_operand(opcode));
                            float dst_f = get_fp_operand((opcode >> 9) & 7);
                            asm("flds %0" : : "m" (dst_f));
                            asm("fdivs %0" : : "m" (src_f));
                            asm("fstps %0" : "=m" (dst_f));
                            uae60_regs.fp[(opcode >> 9) & 7] = set_fp_register(dst_f);
                            update_fpu_flags();
                            break;
                        }
                        case 0xF205: { // FSGLMUL
                            float src_f = *(float*)(amiga_memory + get_src_operand(opcode));
                            float dst_f = get_fp_operand((opcode >> 9) & 7);
                            asm("flds %0" : : "m" (dst_f));
                            asm("fmuls %0" : : "m" (src_f));
                            asm("fstps %0" : "=m" (dst_f));
                            uae60_regs.fp[(opcode >> 9) & 7] = set_fp_register(dst_f);
                            update_fpu_flags();
                            break;
                        }
                        case 0xF228: { // FREM
                            long double src_x = *(long double*)(amiga_memory + get_src_operand(opcode));
                            long double dst_x = get_fp_operand((opcode >> 9) & 7);
                            asm("fldt %0" : : "m" (dst_x));
                            asm("fpremt" 
                                :
                                : );
                            asm("fstpt %0" : "=m" (dst_x));
                            uae60_regs.fp[(opcode >> 9) & 7] = set_fp_register(dst_x);
                            update_fpu_flags();
                            break;
                        }
                        case 0xF229: { // FSCALE
                            long double src_x = *(long double*)(amiga_memory + get_src_operand(opcode));
                            long double dst_x = get_fp_operand((opcode >> 9) & 7);
                            asm("fldt %0" : : "m" (dst_x));
                            asm("fscale"
                                :
                                : );
                            asm("fstpt %0" : "=m" (dst_x));
                            uae60_regs.fp[(opcode >> 9) & 7] = set_fp_register(dst_x);
                            update_fpu_flags();
                            break;
                        }
                        case 0xF208: { // FSQRT.S
                            float dst_f = get_fp_operand((opcode >> 9) & 7);
                            asm("flds %0" : : "m" (dst_f));
                            asm("fsqrts"
                                :
                                : );
                            asm("fstps %0" : "=m" (dst_f));
                            uae60_regs.fp[(opcode >> 9) & 7] = set_fp_register(dst_f);
                            update_fpu_flags();
                            break;
                        }
                        case 0xF218: { // FSQRT.D
                            double dst_d = get_fp_operand((opcode >> 9) & 7);
                            asm("fldl %0" : : "m" (dst_d));
                            asm("fsqrtd"
                                :
                                : );
                            asm("fstpl %0" : "=m" (dst_d));
                            uae60_regs.fp[(opcode >> 9) & 7] = set_fp_register(dst_d);
                            update_fpu_flags();
                            break;
                        }
                        case 0xF228: { // FSQRT.X
                            long double dst_x = get_fp_operand((opcode >> 9) & 7);
                            asm("fldt %0" : : "m" (dst_x));
                            asm("fsqrt"
                                :
                                : );
                            asm("fstpt %0" : "=m" (dst_x));
                            uae60_regs.fp[(opcode >> 9) & 7] = set_fp_register(dst_x);
                            update_fpu_flags();
                            break;
                        }
                        case 0xF209: { // FABS.S
                            float dst_f = get_fp_operand((opcode >> 9) & 7);
                            asm("flds %0" : : "m" (dst_f));
                            asm("fabs"
                                :
                                : );
                            asm("fstps %0" : "=m" (dst_f));
                            uae60_regs.fp[(opcode >> 9) & 7] = set_fp_register(dst_f);
                            update_fpu_flags();
                            break;
                        }
                        case 0xF219: { // FABS.D
                            double dst_d = get_fp_operand((opcode >> 9) & 7);
                            asm("fldl %0" : : "m" (dst_d));
                            asm("fabs"
                                :
                                : );
                            asm("fstpl %0" : "=m" (dst_d));
                            uae60_regs.fp[(opcode >> 9) & 7] = set_fp_register(dst_d);
                            update_fpu_flags();
                            break;
                        }
                        case 0xF229: { // FABS.X
                            long double dst_x = get_fp_operand((opcode >> 9) & 7);
                            asm("fldt %0" : : "m" (dst_x));
                            asm("fabs"
                                :
                                : );
                            asm("fstpt %0" : "=m" (dst_x));
                            uae60_regs.fp[(opcode >> 9) & 7] = set_fp_register(dst_x);
                            update_fpu_flags();
                            break;
                        }
                        case 0xF202: // FCMP.S
                            {
                                float src_f = *(float*)(amiga_memory + get_src_operand(opcode));
                                float dst_f = get_fp_operand((opcode >> 9) & 7);
                                asm("flds %0" : : "m" (src_f));
                                asm("flds %0" : : "m" (dst_f));
                                asm("fcompp" 
                                    :
                                    : );
                                update_fpu_flags();
                                break;
                            }
                        case 0xF212: // FCMP.D
                            {
                                double src_d = *(double*)(amiga_memory + get_src_operand(opcode));
                                double dst_d = get_fp_operand((opcode >> 9) & 7);
                                asm("fldl %0" : : "m" (src_d));
                                asm("fldl %0" : : "m" (dst_d));
                                asm("fcompp" 
                                    :
                                    : );
                                update_fpu_flags();
                                break;
                            }
                        case 0xF222: // FCMP.X
                            {
                                long double src_x = *(long double*)(amiga_memory + get_src_operand(opcode));
                                long double dst_x = get_fp_operand((opcode >> 9) & 7);
                                asm("fldt %0" : : "m" (src_x));
                                asm("fldt %0" : : "m" (dst_x));
                                asm("fcompp"
                                    :
                                    : );
                                update_fpu_flags();
                                break;
                            }
                        case 0xF230: // FINT.S
                            {
                                float value = *(float*)(amiga_memory + get_src_operand(opcode));
                                int32_t result;
                                asm("flds %1"
                                    :
                                    : "m" (value));
                                asm("fistpl %0"
                                    : "=m" (result));
                                uae60_regs.d[(opcode >> 9) & 7] = result;
                                update_fpu_flags();
                                break;
                            }
                        case 0xF231: // FINT.D
                            {
                                double value = *(double*)(amiga_memory + get_src_operand(opcode));
                                int32_t result;
                                asm("fldl %1"
                                    :
                                    : "m" (value));
                                asm("fistpl %0"
                                    : "=m" (result));
                                uae60_regs.d[(opcode >> 9) & 7] = result;
                                update_fpu_flags();
                                break;
                            }
                        case 0xF232: // FINT.X
                            {
                                long double value = *(long double*)(amiga_memory + get_src_operand(opcode));
                                int32_t result;
                                asm("fldt %1"
                                    :
                                    : "m" (value));
                                asm("fistpt %0"
                                    : "=m" (result));
                                uae60_regs.d[(opcode >> 9) & 7] = result;
                                update_fpu_flags();
                                break;
                            }
                        case 0xF234: // FINTRZ.S
                            {
                                float value = *(float*)(amiga_memory + get_src_operand(opcode));
                                int32_t result;
                                asm("flds %1"
                                    :
                                    : "m" (value));
                                asm("fisttpl %0"
                                    : "=m" (result));
                                uae60_regs.d[(opcode >> 9) & 7] = result;
                                update_fpu_flags();
                                break;
                            }
                        case 0xF235: // FINTRZ.D
                            {
                                double value = *(double*)(amiga_memory + get_src_operand(opcode));
                                int32_t result;
                                asm("fldl %1"
                                    :
                                    : "m" (value));
                                asm("fisttpl %0"
                                    : "=m" (result));
                                uae60_regs.d[(opcode >> 9) & 7] = result;
                                update_fpu_flags();
                                break;
                            }
                        case 0xF236: // FINTRZ.X
                            {
                                long double value = *(long double*)(amiga_memory + get_src_operand(opcode));
                                int32_t result;
                                asm("fldt %1"
                                    :
                                    : "m" (value));
                                asm("fistpt %0"
                                    : "=m" (result));
                                uae60_regs.d[(opcode >> 9) & 7] = result;
                                update_fpu_flags();
                                break;
                            }
                        case 0xF23A: { // FTST.S
                            float value = *(float*)(amiga_memory + get_src_operand(opcode));
                            asm("flds %0"
                                :
                                : "m" (value));
                            asm("ftst"
                                :
                                :);
                            update_fpu_flags();
                            break;
                        }
                        case 0xF23B: { // FTST.D
                            double value = *(double*)(amiga_memory + get_src_operand(opcode));
                            asm("fldl %0"
                                :
                                : "m" (value));
                            asm("ftst"
                                :
                                :);
                            update_fpu_flags();
                            break;
                        }
                        case 0xF23C: { // FTST.X
                            long double value = *(long double*)(amiga_memory + get_src_operand(opcode));
                            asm("fldt %0"
                                :
                                : "m" (value));
                            asm("ftst"
                                :
                                :);
                            update_fpu_flags();
                            break;
                        }
                        case 0xF240: // FMOVEM.S (registros a memoria)
                            {
                                uint16_t register_list = get_next_word(uae60_regs.pc);
                                uae60_regs.pc += 2;
                                uint32_t dst_addr = get_dst_operand(opcode);
                                for (int i = 0; i < 8; ++i) {
                                    if (register_list & (1 << i)) {
                                        float value = (float)uae60_regs.fp[i];
                                        *(float*)(amiga_memory + dst_addr) = value;
                                        dst_addr += 4;
                                    }
                                }
                            }
                            break;
                        case 0xF244: // FMOVEM.D (registros a memoria)
                            {
                                uint16_t register_list = get_next_word(uae60_regs.pc);
                                uae60_regs.pc += 2;
                                uint32_t dst_addr = get_dst_operand(opcode);
                                for (int i = 0; i < 8; ++i) {
                                    if (register_list & (1 << i)) {
                                        double value = uae60_regs.fp[i];
                                        *(double*)(amiga_memory + dst_addr) = value;
                                        dst_addr += 8;
                                    }
                                }
                            }
                            break;
                        case 0xF248: // FMOVEM.X (registros a memoria)
                            {
                                uint16_t register_list = get_next_word(uae60_regs.pc);
                                uae60_regs.pc += 2;
                                uint32_t dst_addr = get_dst_operand(opcode);
                                for (int i = 0; i < 8; ++i) {
                                    if (register_list & (1 << i)) {
                                        long double value = uae60_regs.fp[i];
                                        *(long double*)(amiga_memory + dst_addr) = value;
                                        dst_addr += 12;
                                    }
                                }
                            }
                            break;
                        case 0xF24C: // FMOVEM. control (registros a memoria)
                            {
                                uint16_t register_list = get_next_word(uae60_regs.pc);
                                uae60_regs.pc += 2;
                                uint32_t dst_addr = get_dst_operand(opcode);
                                for (int i = 0; i < 8; ++i) {
                                    if (register_list & (1 << i)) {
                                        uint32_t value = 0;
                                        switch (i) {
                                            case 0: value = uae60_regs.fpcr; break;
                                            case 1: value = uae60_regs.fpsr; break;
                                            case 2: value = uae60_regs.fpiar; break;
                                        }
                                        *(uint32_t*)(amiga_memory + dst_addr) = value;
                                        dst_addr += 4;
                                    }
                                }
                            }
                            break;
                        case 0xF250: // FMOVEM.S (memoria a registros)
                            {
                                uint16_t register_list = get_next_word(uae60_regs.pc);
                                uae60_regs.pc += 2;
                                uint32_t src_addr = get_src_operand(opcode);
                                for (int i = 0; i < 8; ++i) {
                                    if (register_list & (1 << i)) {
                                        float value = *(float*)(amiga_memory + src_addr);
                                        uae60_regs.fp[i] = (double)value;
                                        src_addr += 4;
                                    }
                                }
                            }
                            break;
                        case 0xF254: // FMOVEM.D (memoria a registros)
                            {
                                uint16_t register_list = get_next_word(uae60_regs.pc);
                                uae60_regs.pc += 2;
                                uint32_t src_addr = get_src_operand(opcode);
                                for (int i = 0; i < 8; ++i) {
                                    if (register_list & (1 << i)) {
                                        double value = *(double*)(amiga_memory + src_addr);
                                        uae60_regs.fp[i] = value;
                                        src_addr += 8;
                                    }
                                }
                            }
                            break;
                        case 0xF258: // FMOVEM.X (memoria a registros)
                            {
                                uint16_t register_list = get_next_word(uae60_regs.pc);
                                uae60_regs.pc += 2;
                                uint32_t src_addr = get_src_operand(opcode);
                                for (int i = 0; i < 8; ++i) {
                                    if (register_list & (1 << i)) {
                                        long double value = *(long double*)(amiga_memory + src_addr);
                                        uae60_regs.fp[i] = (double)value;
                                        src_addr += 12;
                                    }
                                }
                            }
                            break;
                        case 0xF25C: // FMOVEM. control (memoria a registros)
                            {
                                uint16_t register_list = get_next_word(uae60_regs.pc);
                                uae60_regs.pc += 2;
                                uint32_t src_addr = get_src_operand(opcode);
                                for (int i = 0; i < 8; ++i) {
                                    if (register_list & (1 << i)) {
                                        uint32_t value = *(uint32_t*)(amiga_memory + src_addr);
                                        switch (i) {
                                            case 0: uae60_regs.fpcr = value; break;
                                            case 1: uae60_regs.fpsr = value; break;
                                            case 2: uae60_regs.fpiar = value; break;
                                        }
                                        src_addr += 4;
                                    }
                                }
                            }
                            break;
                        case 0xF260: // FMOVE.L <ea>,FPcr
                            {
                                uint32_t value = get_src_operand(opcode);
                                uae60_regs.fpcr = value;
                            }
                            break;
                        case 0xF268: // FMOVE.L <ea>,FPsr
                            {
                                uint32_t value = get_src_operand(opcode);
                                uae60_regs.fpsr = value;
                            }
                            break;
                        case 0xF270: // FMOVE.L FPcr,<ea>
                            {
                                uint32_t dst_addr = get_dst_operand(opcode);
                                *(uint32_t*)(amiga_memory + dst_addr) = uae60_regs.fpcr;
                            }
                            break;
                        case 0xF278: // FMOVE.L FPsr,<ea>
                            {
                                uint32_t dst_addr = get_dst_operand(opcode);
                                *(uint32_t*)(amiga_memory + dst_addr) = uae60_regs.fpsr;
                            }
                            break;
                        case 0xF310: // FSAVE
                            {
                                uint32_t addr = uae60_regs.a[7] - 12;
                                uae60_regs.a[7] = addr;
                                uint32_t* mem_ptr = (uint32_t*)(amiga_memory + addr);
                                asm volatile("fstenv (%0)" : : "r"(mem_ptr));
                            }
                            break;
                        case 0xF314: // FRESTORE
                            {
                                uint32_t addr = uae60_regs.a[7];
                                uint32_t* mem_ptr = (uint32_t*)(amiga_memory + addr);
                                asm volatile("frstor (%0)" : : "r"(mem_ptr));
                                uae60_regs.a[7] += 12;
                            }
                            break;
                        case 0xF2C0:  // FDBcc.W - F
                        case 0xF2C1:  // FDBcc.W - EQ
                        case 0xF2C2:  // FDBcc.W - OGT
                        case 0xF2C3:  // FDBcc.W - OGE
                        case 0xF2C4:  // FDBcc.W - OLT
                        case 0xF2C5:  // FDBcc.W - OLE
                        case 0xF2C6:  // FDBcc.W - OGL
                        case 0xF2C7:  // FDBcc.W - OR
                        case 0xF2C8:  // FDBcc.W - UN
                        case 0xF2C9:  // FDBcc.W - UEQ
                        case 0xF2CA:  // FDBcc.W - UGT
                        case 0xF2CB:  // FDBcc.W - UGE
                        case 0xF2CC:  // FDBcc.W - ULT
                        case 0xF2CD:  // FDBcc.W - ULE
                        case 0xF2CE:  // FDBcc.W - SF
                        case 0xF2CF:  // FDBcc.W - ST
                            {
                                uint8_t data_reg = (opcode >> 9) & 7;
                                int16_t displacement = (int16_t)get_next_word(uae60_regs.pc);
                                uae60_regs.pc += 2;
                                --uae60_regs.d[data_reg];
                                if (uae60_regs.d[data_reg] == -1) {
                                    break;
                                    uae60_regs.pc += displacement;
                                }
                                uint8_t condition = (opcode & 0x3F);
                                bool shouldBranch = false;
                                uint16_t fpu_status = 0;
                                asm("fstsw %0" : "=m" (fpu_status)); 
                                switch (condition) {
                                    case 0x30: shouldBranch = (fpu_status & 0x4000) != 0; break;  // F - False
                                    case 0x31: shouldBranch = (fpu_status & 0x4000) == 0; break;  // EQ - Equal
                                    case 0x32: shouldBranch = (fpu_status & 0x0400) != 0; break;  // OGT - Ordered Greater Than
                                    case 0x33: shouldBranch = (fpu_status & 0x0400) == 0; break;  // OGE - Ordered Greater or Equal
                                    case 0x34: shouldBranch = (fpu_status & 0x4400) != 0; break;  // OLT - Ordered Less Than
                                    case 0x35: shouldBranch = (fpu_status & 0x4400) == 0; break;  // OLE - Ordered Less or Equal
                                    case 0x36: shouldBranch = (fpu_status & 0x0040) != 0; break;  // OGL - Ordered Greater or Less
                                    case 0x37: shouldBranch = (fpu_status & 0x0040) == 0; break;  // OR - Ordered
                                    case 0x38: shouldBranch = (fpu_status & 0x0400) == 0; break;  // UN - Unordered
                                    case 0x39: shouldBranch = (fpu_status & 0x4000) == 0; break;  // UEQ - Unordered or Equal
                                    case 0x3A: shouldBranch = (fpu_status & 0x0400) != 0; break;  // UGT - Unordered or Greater Than
                                    case 0x3B: shouldBranch = (fpu_status & 0x0400) == 0; break;  // UGE - Unordered or Greater or Equal
                                    case 0x3C: shouldBranch = (fpu_status & 0x4400) != 0; break;  // ULT - Unordered or Less Than
                                    case 0x3D: shouldBranch = (fpu_status & 0x4400) == 0; break;  // ULE - Unordered or Less or Equal
                                    case 0x3E: shouldBranch = (fpu_status & 0x4000) != 0; break;  // SF - Signaling False
                                    case 0x3F: shouldBranch = (fpu_status & 0x4000) == 0; break;  // ST - Signaling True CORTE
                                }
                                if (!shouldBranch) {
                                    uae6                                  _regs.pc += displacement;
                                }
                            }
                            break;
                        case 0xF600: // MOVE16 (Ax)+,(Ay)+
                            {
                                uint32_t src_addr = uae60_regs.a[(opcode >> 9) & 7];
                                uint32_t dst_addr = uae60_regs.a[opcode & 7];
                                for (int i = 0; i < 16; ++i) {
                                    amiga_memory[dst_addr + i] = amiga_memory[src_addr + i];
                                }
                                uae60_regs.a[(opcode >> 9) & 7] += 16;
                                uae60_regs.a[opcode & 7] += 16;
                            }
                            break;
                        case 0xF610: // MOVE16 (xxx).L,(Ay)+
                            {
                                uint32_t src_addr = get_next_long(uae60_regs.pc);
                                uae60_regs.pc += 4;
                                uint32_t dst_addr = uae60_regs.a[opcode & 7];
                                for (int i = 0; i < 16; ++i) {
                                    amiga_memory[dst_addr + i] = amiga_memory[src_addr + i];
                                }
                                uae60_regs.a[opcode & 7] += 16;
                            }
                            break;
                        case 0xF618: // MOVE16 (Ax)+,(xxx).L
                            {
                                uint32_t src_addr = uae60_regs.a[(opcode >> 9) & 7];
                                uint32_t dst_addr = get_next_long(uae60_regs.pc);
                                uae60_regs.pc += 4;
                                for (int i = 0; i < 16; ++i) {
                                    amiga_memory[dst_addr + i] = amiga_memory[src_addr + i];
                                }
                                uae60_regs.a[(opcode >> 9) & 7] += 16;
                            }
                            break;
                        case 0xF500: // PERM Dm,Dn
                            {
                                uint32_t src = uae60_regs.d[(opcode >> 9) & 7];
                                uint8_t pattern = (uint8_t)get_src_operand(opcode);
                                uint32_t result = 0;
                                for (int i = 0; i < 4; ++i) {
                                    uint8_t byte_index = (pattern >> (i * 2)) & 3;
                                    result |= ((src >> (byte_index * 8)) & 0xFF) << (i * 8);
                                }
                                uae60_regs.d[opcode & 7] = result;
                            }
                            break;
                        case 0xF540: // PERM (Am),Dn
                            {
                                uint32_t src = *(uint32_t*)(amiga_memory + get_src_operand(opcode));
                                uint8_t pattern = (uint8_t)get_src_operand(opcode);
                                uint32_t result = 0;
                                for (int i = 0; i < 4; ++i) {
                                    uint8_t byte_index = (pattern >> (i * 2)) & 3;
                                    result |= ((src >> (byte_index * 8)) & 0xFF) << (i * 8);
                                }
                                uae60_regs.d[opcode & 7] = result;
                            }
                            break;
                    } // switch (opcode & 0xF1C0)
                }
                break; // case 0xF

        } // switch (opcode_high)
    } // else (instrucción soportada)

    uae60_regs.pc += 2; // Incrementa el PC para la siguiente instrucción
}

// Función para leer un dato de la memoria emulada
uint32_t uae60_mem_read(uint32_t addr, uint8_t size) {
    // ... (Implementación - Ver Mensaje 00108)
}

// Función para escribir un dato en la memoria emulada
void uae60_mem_write(uint32_t addr, uint8_t size, uint32_t data) {
    // ... (Implementación - Ver Mensaje 00108)
}

// Maneja las llamadas al sistema y excepciones
void uae60_trap(uint16_t trap_nr) {
    // Implementa la lógica para manejar las excepciones usando la API de AROS x86
   // Por ahora, solo se imprime un mensaje de error. 
  // En una fase posterior, implementaremos el manejo adecuado para cada excepción.
    switch (trap_nr) {
        case 2: // Bus Error
            std::cerr << "Excepción de Bus Error (vector 2)" << std::endl;
            // TODO: Implementar el manejo adecuado para Bus Error
            break;
        case 3: // Address Error
            std::cerr << "Excepción de Address Error (vector 3)" << std::endl;
            // TODO: Implementar el manejo adecuado para Address Error
            break;
        case 4: // Illegal Instruction
            std::cerr << "Excepción de Illegal Instruction (vector 4)" << std::endl;
            // TODO: Implementar el manejo adecuado para Illegal Instruction
            break;
        case 5: // Divide by Zero
            std::cerr << "Excepción de Divide by Zero (vector 5)" << std::endl;
            // TODO: Implementar el manejo adecuado para Divide by Zero
            break;
        case 6: // CHK Instruction
            std::cerr << "Excepción de CHK Instruction (vector 6)" << std::endl;
            // TODO: Implementar el manejo adecuado para CHK Instruction
            break;
        case 8: // Privilege Violation
            std::cerr << "Excepción de Privilege Violation (vector 8)" << std::endl;
            // TODO: Implementar el manejo adecuado para Privilege Violation
            break;
        case 9: // Trace
            std::cerr << "Excepción de Trace (vector 9)" << std::endl;
            // TODO: Implementar el manejo adecuado para Trace
            break;
        case 10: // Line 1010 Emulator
            std::cerr << "Excepción de Line 1010 Emulator (vector 10)" << std::endl;
            // TODO: Implementar el manejo adecuado para Line 1010 Emulator
            break;
        case 11: // Line 1111 Emulator
            std::cerr << "Excepción de Line 1111 Emulator (vector 11)" << std::endl;
            // TODO: Implementar el manejo adecuado para Line 1111 Emulator
            break;
        // ... (añadir casos para otros traps)
        default:
            std::cerr << "Excepción no implementada: " << trap_nr << std::endl;
            break;
    }
}

// Función para obtener el operando fuente
uint32_t get_src_operand(uint16_t opcode) {
    uint8_t mode = (opcode >> 3) & 0x7;
    uint8_t reg = opcode & 0x7;

    uint32_t addr = 0; // Valor por defecto

    switch (mode) {
        case 0: // Dn - Data Register Direct
            return uae60_regs.d[reg];
        case 1: // An - Address Register Direct
            return uae60_regs.a[reg];
        case 2: // (An) - Address Register Indirect
            addr = uae60_regs.a[reg];
            break;
        case 3: // (An)+ - Address Register Indirect with Postincrement
            addr = uae60_regs.a[reg];
            uae60_regs.a[reg] += (opcode & 0x0100) ? 2 : 4; // Incrementa 2 para bytes y words, 4 para longs
            break;
        case 4: // -(An) - Address Register Indirect with Predecrement
            uae60_regs.a[reg] -= (opcode & 0x0100) ? 2 : 4; // Decrementa 2 para bytes y words, 4 para longs
            addr = uae60_regs.a[reg];
            break;
        case 5: // (d16,An) - Address Register Indirect with Displacement
            addr = uae60_regs.a[reg] + (int16_t)get_next_word(uae60_regs.pc);
            uae60_regs.pc += 2;
            break;
        case 6: // (d8,An,Xn) - Address Register Indirect with Index (8-bit displacement)
            {
                uint16_t extension = get_next_word(uae60_regs.pc);
                uae60_regs.pc += 2;
                int8_t displacement = (int8_t)(extension & 0xFF);
                uint8_t index_size = (extension >> 11) & 1; // 0 = Word, 1 = Long
                uint8_t index_reg = (extension >> 12) & 0x7;
                uint32_t index = get_index_value(index_reg, index_size);
                addr = uae60_regs.a[reg] + displacement + index * (index_size ? 4 : 2);
            }
            break;
        case 7: // various
            {
                switch (opcode & 0x003F) {
                    case 0x0038: // (xxx).W - Absolute Short Address
                        addr = (uint32_t)(int16_t)get_next_word(uae60_regs.pc);
                        uae60_regs.pc += 2;
                        break;
                    case 0x0039: // (xxx).L - Absolute Long Address
                        addr = get_next_long(uae60_regs.pc);
                        uae60_regs.pc += 4;
                        break;
                    case 0x003A: // (d16,PC) - Program Counter Indirect with Displacement
                        addr = uae60_regs.pc + 2 + (int16_t)get_next_word(uae60_regs.pc); // +2 porque PC apunta a la siguiente instrucción
                        uae60_regs.pc += 2;
                        break;
                    case 0x003B: // (d8,PC,Xn) - Program Counter Indirect with Index (8-bit displacement)
                        {
                            uint16_t extension = get_next_word(uae60_regs.pc);
                            uae60_regs.pc += 2;
                            int8_t displacement = (int8_t)(extension & 0xFF);
                            uint8_t index_size = (extension >> 11) & 1; // 0 = Word, 1 = Long
                            uint8_t index_reg = (extension >> 12) & 0x7;
                            uint32_t index = get_index_value(index_reg, index_size);
                            addr = uae60_regs.pc + 2 + displacement + index * (index_size ? 4 : 2);
                        }
                        break;
                        case 0x003C: // #<data> - Immediate Data
                        if (opcode & 0x0100) { // Operando de 16 bits
                            addr = uae60_regs.pc;
                            uae60_regs.pc += 2;
                        } else { // Operando de 32 bits
                            addr = uae60_regs.pc;
                            uae60_regs.pc += 4;
                        }
                        break;
                    default:
                        printf("Error: Modo de direccionamiento no soportado para get_src_operand: %02X\n", mode);
                        exit(1);
                } // switch (opcode & 0x003F)
            }
            break;
        default:
            printf("Error: Modo de direccionamiento no soportado para get_src_operand: %02X\n", mode);
            exit(1);
    } // switch (mode)
    uint8_t size = (opcode & 0x0100) ? 2 : 4;
    return uae60_mem_read(addr, size);
}

// Función para obtener el operando destino
uint32_t get_dst_operand(uint16_t opcode) {
uint8_t mode = (opcode >> 6) & 0x7;
    uint8_t reg = opcode & 0x7;

    uint32_t addr = 0; // Valor por defecto

    switch (mode) {
        case 0: // Dn - Data Register Direct
            return (uint32_t)&uae60_regs.d[reg]; // Devuelve la dirección del registro de datos
        case 1: // An - Address Register Direct
            return (uint32_t)&uae60_regs.a[reg]; // Devuelve la dirección del registro de direcciones
        case 2: // (An) - Address Register Indirect
            return uae60_regs.a[reg];
        case 3: // (An)+ - Address Register Indirect with Postincrement
            addr = uae60_regs.a[reg];
            uae60_regs.a[reg] += (opcode & 0x0100) ? 2 : 4; // Incrementa 2 para bytes y words, 4 para longs
            return addr;
        case 4: // -(An) - Address Register Indirect with Predecrement
            uae60_regs.a[reg] -= (opcode & 0x0100) ? 2 : 4; // Decrementa 2 para bytes y words, 4 para longs
            return uae60_regs.a[reg];
        case 5: // (d16,An) - Address Register Indirect with Displacement
            addr = uae60_regs.a[reg] + (int16_t)get_next_word(uae60_regs.pc);
            uae60_regs.pc += 2;
            return addr;
        case 6: // (d8,An,Xn) - Address Register Indirect with Index (8-bit displacement)
            {
                uint16_t extension = get_next_word(uae60_regs.pc);
                uae60_regs.pc += 2;
                int8_t displacement = (int8_t)(extension & 0xFF);
                uint8_t index_size = (extension >> 11) & 1; // 0 = Word, 1 = Long
                uint8_t index_reg = (extension >> 12) & 0x7;
                uint32_t index = get_index_value(index_reg, index_size);
                addr = uae60_regs.a[reg] + displacement + index * (index_size ? 4 : 2);
                return addr;
            }
            break;
        case 7: // various
            {
                switch (opcode & 0x003F) {
                    case 0x0038: // (xxx).W - Absolute Short Address
                        addr = (uint32_t)(int16_t)get_next_word(uae60_regs.pc);
                        uae60_regs.pc += 2;
                        return addr;
                    case 0x0039: // (xxx).L - Absolute Long Address
                        addr = get_next_long(uae60_regs.pc);
                        uae60_regs.pc += 4;
                        return addr;
                    case 0x003A: // (d16,PC) - Program Counter Indirect with Displacement
                        addr = uae60_regs.pc + 2 + (int16_t)get_next_word(uae60_regs.pc); // +2 porque PC apunta a la siguiente instrucción
                        uae60_regs.pc += 2;
                        return addr;
                    case 0x003B: // (d8,PC,Xn) - Program Counter Indirect with Index (8-bit displacement)
                        {
                            uint16_t extension = get_next_word(uae60_regs.pc);
                            uae60_regs.pc += 2;
                            int8_t displacement = (int8_t)(extension & 0xFF);
                            uint8_t index_size = (extension >> 11) & 1; // 0 = Word, 1 = Long
                            uint8_t index_reg = (extension >> 12) & 0x7;
                            uint32_t index = get_index_value(index_reg, index_size);
                            addr = uae60_regs.pc + 2 + displacement + index * (index_size ? 4 : 2);
                            return addr;
                        }
                        break;
                    default:
                        printf("Error: Modo de direccionamiento no soportado para get_dst_operand: %02X\n", mode);
                        exit(1);
                } // switch (opcode & 0x003F)
            }
            break;
        default:
            printf("Error: Modo de direccionamiento no soportado para get_dst_operand: %02X\n", mode);
            exit(1);
    } // switch (mode)

    return addr;
}

// Función para actualizar los flags
void update_flags(uint32_t result, uint8_t size) {
// Zero Flag (ZF)
    uae60_regs.sr &= ~(1 << 6); // Borra el flag Zero
    if ((size == 1 && (result & 0xFF) == 0) ||
        (size == 2 && (result & 0xFFFF) == 0) ||
        (size == 4 && result == 0)) {
        uae60_regs.sr |= (1 << 6); // Establece el flag Zero si el resultado es cero
    }

    // Negative Flag (NF)
    uae60_regs.sr &= ~(1 << 7); // Borra el flag Negative
    if ((size == 1 && (result & 0x80) != 0) ||
        (size == 2 && (result & 0x8000) != 0) ||
        (size == 4 && (result & 0x80000000) != 0)) {
        uae60_regs.sr |= (1 << 7); // Establece el flag Negative si el bit más significativo es 1
    }

    // Overflow Flag (VF)
    if (size == 1) {
        // Overflow para bytes
        uae60_regs.sr &= ~(1 << 11); // Borra el flag Overflow
        if (((uae60_regs.d[(opcode >> 9) & 7] ^ result) & 0x80) != 0 && ((uae60_regs.d[(opcode >> 9) & 7] ^ get_src_operand(opcode)) & 0x80) == 0) {
            uae60_regs.sr |= (1 << 11); // Establece el flag Overflow
        }
    }
    else if (size == 2) {
        // Overflow para words
        uae60_regs.sr &= ~(1 << 11); // Borra el flag Overflow
        if (((uae60_regs.d[(opcode >> 9) & 7] ^ result) & 0x8000) != 0 && ((uae60_regs.d[(opcode >> 9) & 7] ^ get_src_operand(opcode)) & 0x8000) == 0) {
            uae60_regs.sr |= (1 << 11); // Establece el flag Overflow
        }
    }
    else {
        // Overflow para longs
        uae60_regs.sr &= ~(1 << 11); // Borra el flag Overflow
        if (((uae60_regs.d[(opcode >> 9) & 7] ^ result) & 0x80000000) != 0 && ((uae60_regs.d[(opcode >> 9) & 7] ^ get_src_operand(opcode)) & 0x80000000) == 0) {
            uae60_regs.sr |= (1 << 11); // Establece el flag Overflow
        }
    }

    // Carry Flag (CF)
    uae60_regs.sr &= ~(1 << 0); // Borra el flag Carry
    if (size == 1) {
        // Carry para bytes
        if ((result & 0x100) != 0) {
            uae60_regs.sr |= (1 << 0); // Establece el flag Carry
        }
    }
    else if (size == 2) {
        // Carry para words
        if ((result & 0x10000) != 0) {
            uae60_regs.sr |= (1 << 0); // Establece el flag Carry
        }
    }
    else {
        // Carry para longs
        if ((uint64_t)uae60_regs.d[(opcode >> 9) & 7] + (uint64_t)get_src_operand(opcode) > 0xFFFFFFFF) {
            uae60_regs.sr |= (1 << 0); // Establece el flag Carry
        }
    }
}

// Función para verificar si estamos en modo supervisor
bool is_supervisor_mode() {
   return (uae60_regs.sr & 0x2000) != 0; // Bit 13 del SR indica el modo supervisor
}

// Función para obtener el manejador de la trap correspondiente al opcode
trap_handler_t get_trap_handler(uint16_t opcode) {
for (const auto& entry : m68k_trap_table) {
        if (entry.opcode == opcode) {
            return entry.handler;
        }
    }
    // No se encontró un manejador de trap
    return nullptr;
}

// Función para traducir la estructura ViewPort de AmigaOS 3.x a tags de AROS x86
struct TagItem* translate_viewport(struct ViewPort* vp) {
// Crear una lista de tags
    TagItem tags[16]; // Asigna un tamaño suficiente para los tags
    int tag_index = 0;

    // Profundidad de color
    tags[tag_index++].ti_Tag = SA_Depth;
    tags[tag_index++].ti_Data = (ULONG)vp->vp_Modes & 0x7;

    // ID de la pantalla
    tags[tag_index++].ti_Tag = SA_DisplayID;
    tags[tag_index++].ti_Data = (ULONG)vp->vp_Modes & 0x7;

    // Ancho en píxeles
    tags[tag_index++].ti_Tag = SA_Width;
    tags[tag_index++].ti_Data = (ULONG)vp->vp_RasInfo->BitMap->BytesPerRow * 8;

    // Alto en píxeles
    tags[tag_index++].ti_Tag = SA_Height;
    tags[tag_index++].ti_Data = (ULONG)vp->vp_RasInfo->BitMap->Rows;

    // Modo de alta resolución (Highres)
    if (vp->vp_Modes & HIRES) {
        tags[tag_index++].ti_Tag = SA_Highres;
        tags[tag_index++].ti_Data = 1;
    }

    // Modo entrelazado (Interlace)
    if (vp->vp_Modes & LACE) {
        tags[tag_index++].ti_Tag = SA_Interlace;
        tags[tag_index++].ti_Data = 1;
    }

    // Modo Hold-And-Modify (HAM)
    if (vp->vp_Modes & HAM) {
        tags[tag_index++].ti_Tag = SA_Ham;
        tags[tag_index++].ti_Data = 1;
    }

    // Modo Extra Half Brite (EXTRA_HALFBRITE)
    if (vp->vp_Modes & EXTRA_HALFBRITE) {
        tags[tag_index++].ti_Tag = SA_ExtraHalfBrite;
        tags[tag_index++].ti_Data = 1;
    }

    // Borde en blanco (BorderBlank)
    if (vp->vp_Flags & VPF_BORDERBLANK) {
        tags[tag_index++].ti_Tag = SA_BorderBlank;
        tags[tag_index++].ti_Data = 1;
    }

    // Traducir la lista de Copper
    struct TagItem* copper_tags = translate_coplist(vp->vp_UCopIns);

    // Insertar los tags de Copper en la lista principal
    int copper_tag_count = 0;
    while (copper_tags[copper_tag_count].ti_Tag != TAG_END) {
        copper_tag_count++;
    }

    // Mover los tags existentes para hacer espacio para los tags de Copper
    for (int i = tag_index - 1; i >= 4; i--) {
        tags[i + copper_tag_count] = tags[i];
    }

    // Copiar los tags de Copper a la lista principal
    for (int i = 0; i < copper_tag_count; i++) {
        tags[4 + i] = copper_tags[i];
    }
    tag_index += copper_tag_count;

    // Traducir el RastPort
    // Añadir tags para los campos relevantes de vp_RasInfo
    tags[tag_index++].ti_Tag = GA_DrawMode;
    tags[tag_index++].ti_Data = (ULONG)vp->vp_RasInfo->DrawMode;

    tags[tag_index++].ti_Tag = GA_FgPen;
    tags[tag_index++].ti_Data = (ULONG)vp->vp_RasInfo->FgPen;

    tags[tag_index++].ti_Tag = GA_BgPen;
    tags[tag_index++].ti_Data = (ULONG)vp->vp_RasInfo->BpPen;

    tags[tag_index++].ti_Tag = GA_AOLPen;
    tags[tag_index++].ti_Data = (ULONG)vp->vp_RasInfo->AOLPen;

    tags[tag_index++].ti_Tag = GA_AreaPt;
    tags[tag_index++].ti_Data = (ULONG)&vp->vp_RasInfo->AreaPt;

    tags[tag_index++].ti_Tag = GA_AreaInfo;
    tags[tag_index++].ti_Data = (ULONG)&vp->vp_RasInfo->AreaInfo;

    // Añadir el tag de fin de lista
    tags[tag_index++].ti_Tag = TAG_END; 
    tags[tag_index++].ti_Data = 0;

    // Devolver la lista de tags
    return tags; 
}

// Función para traducir la estructura CopList de AmigaOS 3.x a una lista de tags de AROS x86
struct TagItem* translate_coplist(struct CopList* cl) {
   // Crear una lista de tags
    std::vector<TagItem> tags; 

    // Obtener el puntero a la primera instrucción
    struct CopIns* cop_instr = cl->cl_First; 

    // Iterar por la lista de instrucciones
    while (cop_instr != nullptr) {
        // Traducir la instrucción a uno o más tags
        switch (cop_instr->ci_Opcode) {
            case COP_MOVE:
                {
                    uint16_t register_address = cop_instr->ci_Register;
                    uint16_t value = cop_instr->ci_Value;

                    // Traducir la instrucción MOVE a tags
                    switch (register_address) {
                        case COLOR00:
                            tags.push_back({ GA_COLOR_REG, 0 });
                            tags.push_back({ GA_COLOR_VALUE, (ULONG)value });
                            break;
                        // ... (casos para otros registros de color)
                        case COLOR01:
                            tags.push_back({ GA_COLOR_REG, 1 });
                            tags.push_back({ GA_COLOR_VALUE, (ULONG)value });
                            break;
                        case COLOR02:
                            tags.push_back({ GA_COLOR_REG, 2 });
                            tags.push_back({ GA_COLOR_VALUE, (ULONG)value });
                            break;
                        case COLOR03:
                            tags.push_back({ GA_COLOR_REG, 3 });
                            tags.push_back({ GA_COLOR_VALUE, (ULONG)value });
                            break;
                        case COLOR04:
                            tags.push_back({ GA_COLOR_REG, 4 });
                            tags.push_back({ GA_COLOR_VALUE, (ULONG)value });
                            break;
                        case COLOR05:
                            tags.push_back({ GA_COLOR_REG, 5 });
                            tags.push_back({ GA_COLOR_VALUE, (ULONG)value });
                            break;
                        case COLOR06:
                            tags.push_back({ GA_COLOR_REG, 6 });
                            tags.push_back({ GA_COLOR_VALUE, (ULONG)value });
                            break;
                        case COLOR07:
                            tags.push_back({ GA_COLOR_REG, 7 });
                            tags.push_back({ GA_COLOR_VALUE, (ULONG)value });
                            break;
                        case COLOR08:
                            tags.push_back({ GA_COLOR_REG, 8 });
                            tags.push_back({ GA_COLOR_VALUE, (ULONG)value });
                            break;
                        case COLOR09:
                            tags.push_back({ GA_COLOR_REG, 9 });
                            tags.push_back({ GA_COLOR_VALUE, (ULONG)value });
                            break;
                        case COLOR10:
                            tags.push_back({ GA_COLOR_REG, 10 });
                            tags.push_back({ GA_COLOR_VALUE, (ULONG)value });
                            break;
                        case COLOR11:
                            tags.push_back({ GA_COLOR_REG, 11 });
                            tags.push_back({ GA_COLOR_VALUE, (ULONG)value });
                            break;
                        case COLOR12:
                            tags.push_back({ GA_COLOR_REG, 12 });
                            tags.push_back({ GA_COLOR_VALUE, (ULONG)value });
                            break;
                        case COLOR13:
                            tags.push_back({ GA_COLOR_REG, 13 });
                            tags.push_back({ GA_COLOR_VALUE, (ULONG)value });
                            break;
                        case COLOR14:
                            tags.push_back({ GA_COLOR_REG, 14 });
                            tags.push_back({ GA_COLOR_VALUE, (ULONG)value });
                            break;
                        case COLOR15:
                            tags.push_back({ GA_COLOR_REG, 15 });
                            tags.push_back({ GA_COLOR_VALUE, (ULONG)value });
                            break;
                        case COLOR16:
                            tags.push_back({ GA_COLOR_REG, 16 });
                            tags.push_back({ GA_COLOR_VALUE, (ULONG)value });
                            break;
                        case COLOR17:
                            tags.push_back({ GA_COLOR_REG, 17 });
                            tags.push_back({ GA_COLOR_VALUE, (ULONG)value });
                            break;
                        case COLOR18:
                            tags.push_back({ GA_COLOR_REG, 18 });
                            tags.push_back({ GA_COLOR_VALUE, (ULONG)value });
                            break;
                        case COLOR19:
                            tags.push_back({ GA_COLOR_REG, 19 });
                            tags.push_back({ GA_COLOR_VALUE, (ULONG)value });
                            break;
                        case COLOR20:
                            tags.push_back({ GA_COLOR_REG, 20 });
                            tags.push_back({ GA_COLOR_VALUE, (ULONG)value });
                            break;
                        case COLOR21:
                            tags.push_back({ GA_COLOR_REG, 21 });
                            tags.push_back({ GA_COLOR_VALUE, (ULONG)value });
                            break;
                        case COLOR22:
                            tags.push_back({ GA_COLOR_REG, 22 });
                            tags.push_back({ GA_COLOR_VALUE, (ULONG)value });
                            break;
                        case COLOR23:
                            tags.push_back({ GA_COLOR_REG, 23 });
                            tags.push_back({ GA_COLOR_VALUE, (ULONG)value });
                            break;
                        case COLOR24:
                            tags.push_back({ GA_COLOR_REG, 24 });
                            tags.push_back({ GA_COLOR_VALUE, (ULONG)value });
                            break;
                        case COLOR25:
                            tags.push_back({ GA_COLOR_REG, 25 });
                            tags.push_back({ GA_COLOR_VALUE, (ULONG)value });
                            break;
                        case COLOR26:
                            tags.push_back({ GA_COLOR_REG, 26 });
                            tags.push_back({ GA_COLOR_VALUE, (ULONG)value });
                            break;
                        case COLOR27:
                            tags.push_back({ GA_COLOR_REG, 27 });
                            tags.push_back({ GA_COLOR_VALUE, (ULONG)value });
                            break;
                        case COLOR28:
                            tags.push_back({ GA_COLOR_REG, 28 });
                            tags.push_back({ GA_COLOR_VALUE, (ULONG)value });
                            break;
                        case COLOR29:
                            tags.push_back({ GA_COLOR_REG, 29 });
                            tags.push_back({ GA_COLOR_VALUE, (ULONG)value });
                            break;
                        case COLOR30:
                            tags.push_back({ GA_COLOR_REG, 30 });
                            tags.push_back({ GA_COLOR_VALUE, (ULONG)value });
                            break;
                        case COLOR31:
                            tags.push_back({ GA_COLOR_REG, 31 });
                            tags.push_back({ GA_COLOR_VALUE, (ULONG)value });
                            break;
                        case BPLCON0:
                            tags.push_back({ GA_BPLCON0, (ULONG)value });
                            break;
                        case BPLCON1:
                            tags.push_back({ GA_BPLCON1, (ULONG)value });
                            break;
                        case BPL1PTH:
                            tags.push_back({ GA_BPL1PTH, (ULONG)value });
                            break;
                        case BPL1PTL:
                            tags.push_back({ GA_BPL1PTL, (ULONG)value });
                            break;
                        case BPL2PTH:
                            tags.push_back({ GA_BPL2PTH, (ULONG)value });
                            break;
                        case BPL2PTL:
                            tags.push_back({ GA_BPL2PTL, (ULONG)value });
                            break;
                        case BPL3PTH:
                            tags.push_back({ GA_BPL3PTH, (ULONG)value });
                            break;
                        case BPL3PTL:
                            tags.push_back({ GA_BPL3PTL, (ULONG)value });
                            break;
                        case BPL4PTH:
                            tags.push_back({ GA_BPL4PTH, (ULONG)value });
                            break;
                        case BPL4PTL:
                            tags.push_back({ GA_BPL4PTL, (ULONG)value });
                            break;
                        case BPL5PTH:
                            tags.push_back({ GA_BPL5PTH, (ULONG)value });
                            break;
                        case BPL5PTL:
                            tags.push_back({ GA_BPL5PTL, (ULONG)value });
                            break;
                        case BPL6PTH:
                            tags.push_back({ GA_BPL6PTH, (ULONG)value });
                            break;
                        case BPL6PTL:
                            tags.push_back({ GA_BPL6PTL, (ULONG)value });
                            break;
                        case DDFSTRT:
                            tags.push_back({ GA_DDFSTRT, (ULONG)value });
                            break;
                        case DDFSTOP:
                            tags.push_back({ GA_DDFSTOP, (ULONG)value });
                            break;
                        case SPR0PTH: case SPR1PTH: case SPR2PTH: case SPR3PTH:
                        case SPR4PTH: case SPR5PTH: case SPR6PTH: case SPR7PTH:
                            tags.push_back({ GA_SPRITE_POINTER + (register_address - SPR0PTH) / 4, (ULONG)value });
                            break;
                        case SPR0PTL: case SPR1PTL: case SPR2PTL: case SPR3PTL:
                        case SPR4PTL: case SPR5PTL: case SPR6PTL: case SPR7PTL:
                            tags.push_back({ GA_SPRITE_POINTER + (register_address - SPR0PTL) / 4, (ULONG)value });
                            break;
                        case SPR0POS: case SPR1POS: case SPR2POS: case SPR3POS:
                        case SPR4POS: case SPR5POS: case SPR6POS: case SPR7POS:
                            tags.push_back({ GA_SPRITE_POSITION + (register_address - SPR0POS) / 2, (ULONG)value });
                            break;
                        case SPR0CTL: case SPR1CTL: case SPR2CTL: case SPR3CTL:
                        case SPR4CTL: case SPR5CTL: case SPR6CTL: case SPR7CTL:
                            tags.push_back({ GA_SPRITE_CONTROL + (register_address - SPR0CTL) / 2, (ULONG)value });
                            break;
                        case AUD0LCH: case AUD1LCH: case AUD2LCH: case AUD3LCH:
                            tags.push_back({ GA_AUDIO_CHANNEL_LCH + (register_address - AUD0LCH) / 4, (ULONG)value });
                            break;
                        case AUD0LCL: case AUD1LCL: case AUD2LCL: case AUD3LCL:
                            tags.push_back({ GA_AUDIO_CHANNEL_LCL + (register_address - AUD0LCL) / 4, (ULONG)value });
                            break;
                        case AUD0LEN: case AUD1LEN: case AUD2LEN: case AUD3LEN:
                            tags.push_back({ GA_AUDIO_CHANNEL_LEN + (register_address - AUD0LEN) / 4, (ULONG)value });
                            break;
                        case AUD0PER: case AUD1PER: case AUD2PER: case AUD3PER:
                            tags.push_back({ GA_AUDIO_CHANNEL_PER + (register_address - AUD0PER) / 4, (ULONG)value });
                            break;
                        case AUD0VOL: case AUD1VOL: case AUD2VOL: case AUD3VOL:
                            tags.push_back({ GA_AUDIO_CHANNEL_VOL + (register_address - AUD0VOL) / 4, (ULONG)value });
                            break;
                        case DMACON:
                            tags.push_back({ GA_DMACON, (ULONG)value });
                            break;
                        case INTENA:
                            tags.push_back({ GA_INTENA, (ULONG)value });
                            break;
                        case INTREQ:
                            tags.push_back({ GA_INTREQ, (ULONG)value });
                            break;
                        case ADKCON:
                            tags.push_back({ GA_ADKCON, (ULONG)value });
                            break;
                        default:
                            std::cerr << "Error: Registro de Copper no soportado: " << std::hex << register_address << std::endl;
                            break;
                    }
                }
                break;
            case COP_WAIT:
                {
                    uint16_t vertical_position = cop_instr->ci_Vp;
                    uint16_t horizontal_position = cop_instr->ci_Hp;

                    // Calcular el tiempo de espera en microsegundos
                    // Asumimos una frecuencia de refresco de 60 Hz (16.67 ms por frame)
                    uint32_t wait_time_us = (vertical_position * 16667) / 256 + (horizontal_position * 64) / 256;

                    // Añadir un tag para la espera
                    tags.push_back({ GA_WAIT_TIME, wait_time_us });
                }
                break;

            case COP_SKIP:
                {
                    uint16_t vertical_position = cop_instr->ci_Vp;
                    uint16_t horizontal_position = cop_instr->ci_Hp;

                    // Calcular el ciclo de renderizado correspondiente a la posición del haz
                    uint32_t target_cycle = (vertical_position * HORIZONTAL_SCANLINES) + horizontal_position;

                    // Añadir un tag para la condición
                    tags.push_back({ GA_SKIP_IF, (render_cycle_count >= target_cycle) });
                }
                break;

            default:
                std::cerr << "Error: Código de operación de Copper no válido: " << std::hex << cop_instr->ci_Opcode << std::endl;
                break;
        }

        // Avanzar a la siguiente instrucción
        cop_instr = cop_instr->ci_Next;
    }

    // Añadir el tag de fin de lista
    tags.push_back({ TAG_END, 0 });

    // Convertir la lista de tags a un array
    TagItem* tag_array = new TagItem[tags.size()];
    std::copy(tags.begin(), tags.end(), tag_array);

    return tag_array;
}

// Función para traducir la estructura NewView a tags de AROS x86
struct TagItem* translate_newview(struct NewView* newView) {
    // Crear una lista de tags
    std::vector<TagItem> tags;

    // Traducir nv_Modes y nv_Flags
    if (newView->nv_Modes & HIRES) {
        tags.push_back({ SA_Highres, 1 });
    }
    if (newView->nv_Modes & LACE) {
        tags.push_back({ SA_Interlace, 1 });
    }
    if (newView->nv_Modes & HAM) {
        tags.push_back({ SA_Ham, 1 });
    }
    if (newView->nv_Modes & EXTRA_HALFBRITE) {
        tags.push_back({ SA_ExtraHalfBrite, 1 });
    }
    // TODO: Añadir traducción para otros modos de pantalla si es necesario.

    if (newView->nv_Flags & NEWVIEW_BorderBlank) {
        tags.push_back({ SA_BorderBlank, 1 });
    }
    if (newView->nv_Flags & NEWVIEW_Exclusive) {
        tags.push_back({ SA_Exclusive, 1 });
    }
    if (newView->nv_Flags & NEWVIEW_BackFill) {
        tags.push_back({ SA_BackFill, 1 });
    }
    // TODO: Añadir traducción para otros flags si es necesario.

    // Traducir la lista de Copper
    struct TagItem* copper_tags = translate_coplist(newView->nv_CopperList);

    // Añadir los tags de Copper a la lista
    int copper_tag_count = 0;
    while (copper_tags[copper_tag_count].ti_Tag != TAG_END) {
        tags.push_back(copper_tags[copper_tag_count]);
        copper_tag_count++;
    }
    delete[] copper_tags;

    // Añadir el tag de fin de lista
    tags.push_back({ TAG_END, 0 });

    // Convertir la lista de tags a un array
    TagItem* tag_array = new TagItem[tags.size()];
    std::copy(tags.begin(), tags.end(), tag_array);

    return tag_array;
}

// Función para obtener el ViewPort de AROS x86 correspondiente a un ViewPort de AmigaOS 3.x
struct ViewPort* get_aros_viewport(struct ViewPort* amiga_vp) {
    auto it = viewport_map.find(amiga_vp);
    if (it != viewport_map.end()) {
        return it->second;
    } else {
        return nullptr; // No se encontró el ViewPort
    }
}

// Asigna un bloque de memoria
uae_u32 uae60_AllocMem(uae_u32 size, uae_u32 flags) {
    // Calcular la alineación
    uint32_t alignment = (flags & 0xFF) ? (flags & 0xFF) : 4; // Alineación por defecto: 4 bytes

    // Alinear el puntero a la memoria libre
    amiga_memory_free = (uint8_t*)(((uint32_t)amiga_memory_free + alignment - 1) & ~(alignment - 1));

    // Verificar si hay suficiente memoria libre
    if (amiga_memory_free + size > amiga_memory_start + AMIGA_MEMORY_SIZE) {
        std::cerr << "Error: No hay suficiente memoria libre." << std::endl;
        return 0; // Error
    }

    // Asignar el bloque de memoria
    uae_u32 addr = (uae_u32)amiga_memory_free;
    amiga_memory_free += size;

    // Registrar la asignación en la tabla
    memory_allocations.push_back({ addr, size, flags });

    return addr;
}

// Libera un bloque de memoria
void uae60_FreeMem(uae_u32 addr, uae_u32 size) {
    // Buscar la asignación correspondiente en la tabla
    for (auto it = memory_allocations.begin(); it != memory_allocations.end(); ++it) {
        if (it->addr == addr && it->size == size) {
            // Eliminar la asignación de la tabla
            memory_allocations.erase(it);

            // TODO: Implementar la lógica de liberación de memoria en QEMU/KVM
            // (opcional). En esta fase, podríamos simplemente marcar el bloque
            // como libre en la tabla de asignaciones.
            break;
        }
    }
}

// Devuelve la cantidad de memoria libre disponible
uae_u32 uae60_AvailMem(uae_u32 flags) {
    // Traducir los flags de memoria
    uint32_t aros_flags = translate_amiga_mem_flags(flags);

    // Obtener la cantidad de memoria libre de AROS x86
    return IExec->AvailMem(aros_flags);
}

// Abre un archivo
uae_u32 uae60_Open(const char* name, uae_u32 mode) {
    // Traducción de nombres de archivo de AmigaOS a Linux
    std::string linux_name = translate_amiga_filename(name);

    // Traducción de modos de apertura de AmigaOS a Linux
    int linux_mode = translate_amiga_open_mode(mode);

    // Abre el archivo en el host
    int fd = open(linux_name.c_str(), linux_mode);

    // Comprueba si hubo un error al abrir el archivo
    if (fd == -1) {
        std::cerr << "Error: uae60_Open() - No se pudo abrir el archivo '" << name << "'." << std::endl;
        return 0;
    }

    // Devuelve el descriptor del archivo
    return (uae_u32)fd;
}

// Cierra un archivo
void uae60_Close(uae_u32 file) {
    // Cierra el archivo en el host
    close((int)file);
}

// Lee datos de un archivo
uae_u32 uae60_Read(uae_u32 file, void* buffer, uae_u32 length) {
    // Lee datos del archivo en Linux
    ssize_t bytes_read = read((int)file, buffer, length);

    // Comprueba si hubo un error
    if (bytes_read == -1) {
        std::cerr << "Error: uae60_Read() - No se pudieron leer datos del archivo." << std::endl;
        return 0;
    }

    // Devuelve la cantidad de bytes leídos
    return (uae_u32)bytes_read;
}

// Escribe datos en un archivo
uae_u32 uae60_Write(uae_u32 file, const void* buffer, uae_u32 length) {
    // Escribe datos en el archivo en Linux
    ssize_t bytes_written = write((int)file, buffer, length);

    // Comprueba si hubo un error
    if (bytes_written == -1) {
        std::cerr << "Error: uae60_Write() - No se pudieron escribir datos en el archivo." << std::endl;
        return 0;
    }

    // Devuelve la cantidad de bytes escritos
    return (uae_u32)bytes_written;
}

// Función para traducir nombres de archivo de AmigaOS a Linux
std::string translate_amiga_filename(const char* amiga_name) {
    std::string linux_name = amiga_name;

    // Reemplaza los dos puntos por barras inclinadas
    std::replace(linux_name.begin(), linux_name.end(), ':', '/');

    return linux_name;
}

// Función para traducir modos de apertura de AmigaOS a Linux
int translate_amiga_open_mode(uae_u32 amiga_mode) {
    int linux_mode = 0;

    // Modo de lectura
    if (amiga_mode & MODE_OLDFILE) {
        linux_mode |= O_RDONLY;
    }

    // Modo de escritura
    if (amiga_mode & MODE_NEWFILE) {
        linux_mode |= O_WRONLY | O_CREAT | O_TRUNC;
    }

    // Modo de lectura y escritura
    if (amiga_mode & MODE_READWRITE) {
        linux_mode |= O_RDWR;
    }

    // Modo de añadir (append)
    if (amiga_mode & MODE_APPEND) {
        linux_mode |= O_APPEND;
    }

    return linux_mode;
}

// Crea un proceso
struct MsgPort* uae60_CreateProc(const char* name, ULONG pri, struct MsgPort* port, ULONG stackSize) {
    // Crear un MsgPort de AROS x86
    struct MsgPort* aros_port = IExec->CreatePort(name, 0);

    if (aros_port == nullptr) {
        std::cerr << "Error: No se pudo crear el puerto de mensajes." << std::endl;
        return nullptr;
    }

    // Mapear los campos relevantes
    aros_port->mp_Node.ln_Name = (char*)name;
    aros_port->mp_Flags = translate_msgport_flags(port->mp_Flags);

    // Crear el proceso usando la API de AROS x86
    aros_process = IExec->CreateProcess(name, (char*)name, (void (*)())initPC, stackSize, pri);

    if (aros_process == nullptr) {
        std::cerr << "Error: No se pudo crear el proceso." << std::endl;
        IExec->DeletePort(aros_port);
        return nullptr; 
    }

    // Devolver el puntero al MsgPort de AmigaOS 3.x
    return port;
}

// Crea un nuevo proceso
struct MsgPort* uae60_CreateNewProc(const char* name, ULONG pri, struct MsgPort* port, ULONG stackSize, APTR initPC, APTR finalPC) {
    // Crear un MsgPort de AROS x86
    struct MsgPort* aros_port = IExec->CreatePort(name, 0);

    if (aros_port == nullptr) {
        std::cerr << "Error: No se pudo crear el puerto de mensajes." << std::endl;
        return nullptr;
    }

    // Mapear los campos relevantes
    aros_port->mp_Node.ln_Name = (char*)name;
    aros_port->mp_Flags = translate_msgport_flags(port->mp_Flags);

    // Crear el proceso usando la API de AROS x86
    aros_process = IExec->CreateProcess(name, (char*)name, (void (*)())initPC, stackSize, pri);

    if (aros_process == nullptr) {
        std::cerr << "Error: No se pudo crear el proceso." << std::endl;
        IExec->DeletePort(aros_port);
        return nullptr;
    }

    // Devolver el puntero al MsgPort de AmigaOS 3.x
    return port;
}

// Finaliza la ejecución de UAE60
void uae60_Exit(LONG returnCode) {
    // Finalizar el hilo actual
    std::exit(returnCode);
}

// Abre una librería
struct Library* uae60_OpenLibrary(const char* libName, ULONG version) {
    // Adaptar el nombre de la librería a las convenciones de AROS x86 (si es necesario)
    std::string aros_libname = libName;
    std::replace(aros_libname.begin(), aros_libname.end(), '.', '_');

    // Abrir la librería usando la API de AROS x86
    return IExec->OpenLibrary(aros_libname.c_str(), version); 
}

// Cierra una librería
void uae60_CloseLibrary(struct Library* library) {
    IExec->CloseLibrary(library); 
}

// Suma una librería (no se usa en AROS x86)
void uae60_SumLibrary(struct Library* library) {
    // No se hace nada
}

// Deshabilita la multitarea.
void uae60_Forbid() {
    // Deshabilitar la multitarea en AROS
    IExec->Disable();
}

// Reanuda la multitarea.
void uae60_Permit() {
    // Habilitar la multitarea en AROS
    IExec->Enable();
}

// Establece la prioridad de una tarea (si no se especifica, se usa la tarea actual).
ULONG uae60_SetTaskPri(struct Task* task, LONG pri) {
    if (task == nullptr) {
        task = IExec->FindTask(nullptr); // Obtiene la tarea actual si no se especifica
    }
    return IExec->SetTaskPri(task, pri);
}

// Suspende la ejecución durante un tiempo determinado.
void uae60_Delay(ULONG unit) {
    IDelay->Delay(unit);
}

// Función para traducir la estructura NewView a tags de AROS x86
struct TagItem* translate_newview(struct NewView* newView) {
    // Crear una lista de tags
    std::vector<TagItem> tags;

    // Traducir nv_Modes y nv_Flags
    if (newView->nv_Modes & HIRES) {
        tags.push_back({ SA_Highres, 1 });
    }
    if (newView->nv_Modes & LACE) {
        tags.push_back({ SA_Interlace, 1 });
    }
    if (newView->nv_Modes & HAM) {
        tags.push_back({ SA_Ham, 1 });
    }
    if (newView->nv_Modes & EXTRA_HALFBRITE) {
        tags.push_back({ SA_ExtraHalfBrite, 1 });
    }
    if (newView->nv_Modes & DUALPF) {
        tags.push_back({ SA_DoublePlayfield, 1 });
    }
    // TODO: Añadir traducción para otros modos de pantalla si es necesario.

    if (newView->nv_Flags & NEWVIEW_BorderBlank) {
        tags.push_back({ SA_BorderBlank, 1 });
    }
    if (newView->nv_Flags & NEWVIEW_Exclusive) {
        tags.push_back({ SA_Exclusive, 1 });
    }
    if (newView->nv_Flags & NEWVIEW_BackFill) {
        tags.push_back({ SA_BackFill, 1 });
    }
    // TODO: Añadir traducción para otros flags si es necesario.

    // Traducir la lista de Copper
    struct TagItem* copper_tags = translate_coplist(newView->nv_CopperList);

    // Añadir los tags de Copper a la lista
    int copper_tag_count = 0;
    while (copper_tags[copper_tag_count].ti_Tag != TAG_END) {
        tags.push_back(copper_tags[copper_tag_count]);
        copper_tag_count++;
    }
    delete[] copper_tags;

    // Añadir el tag de fin de lista
    tags.push_back({ TAG_END, 0 });

    // Convertir la lista de tags a un array
    TagItem* tag_array = new TagItem[tags.size()];
    std::copy(tags.begin(), tags.end(), tag_array);

    return tag_array;
}

// Función para obtener el ViewPort de AROS x86 correspondiente a un ViewPort de AmigaOS 3.x
struct ViewPort* get_aros_viewport(struct ViewPort* amiga_vp) {
    auto it = viewport_map.find(amiga_vp);
    if (it != viewport_map.end()) {
        return it->second;
    } else {
        return nullptr; // No se encontró el ViewPort
    }
}

// Asigna un bloque de memoria
uae_u32 uae60_AllocMem(uae_u32 size, uae_u32 flags) {
    // Calcular la alineación
    uint32_t alignment = (flags & 0xFF) ? (flags & 0xFF) : 4; // Alineación por defecto: 4 bytes

    // Alinear el puntero a la memoria libre
    amiga_memory_free = (uint8_t*)(((uint32_t)amiga_memory_free + alignment - 1) & ~(alignment - 1));

    // Verificar si hay suficiente memoria libre
    if (amiga_memory_free + size > amiga_memory_start + AMIGA_MEMORY_SIZE) {
        std::cerr << "Error: No hay suficiente memoria libre." << std::endl;
        return 0; // Error
    }

    // Asignar el bloque de memoria
    uae_u32 addr = (uae_u32)amiga_memory_free;
    amiga_memory_free += size;

    // Registrar la asignación en la tabla
    memory_allocations.push_back({ addr, size, flags });

    return addr;
}

// Libera un bloque de memoria
void uae60_FreeMem(uae_u32 addr, uae_u32 size) {
    // Buscar la asignación correspondiente en la tabla
    for (auto it = memory_allocations.begin(); it != memory_allocations.end(); ++it) {
        if (it->addr == addr && it->size == size) {
            // Eliminar la asignación de la tabla
            memory_allocations.erase(it);
            break;
        }
    }
}

// Devuelve la cantidad de memoria libre disponible
uae_u32 uae60_AvailMem(uae_u32 flags) {
    // Traducir los flags de memoria
    uint32_t aros_flags = translate_amiga_mem_flags(flags);

    // Obtener la cantidad de memoria libre de AROS x86
    return IExec->AvailMem(aros_flags);
}


// Devuelve la cantidad de memoria libre disponible
uae_u32 uae60_AvailMem(uae_u32 flags) {
    // Traducir los flags de memoria
    uint32_t aros_flags = translate_amiga_mem_flags(flags);

    // Obtener la cantidad de memoria libre de AROS x86
    return IExec->AvailMem(aros_flags);
}


// Abre un archivo


// Cierra un archivo
void uae60_Close(uae_u32 file) {
    // ... (código de la función - Ver Mensaje 00146)
}

// Lee datos de un archivo
uae_u32 uae60_Read(uae_u32 file, void* buffer, uae_u32 length) {
    // ... (código de la función - Ver Mensaje 00146)
}

// Escribe datos en un archivo
uae_u32 uae60_Write(uae_u32 file, const void* buffer, uae_u32 length) {
    // ... (código de la función - Ver Mensaje 00146)
}

// Crea un proceso
struct MsgPort* uae60_CreateProc(const char* name, ULONG pri, struct MsgPort* port, ULONG stackSize) {
    // ... (código de la función - Ver Mensaje 00862)
}

// Crea un nuevo proceso
struct MsgPort* uae60_CreateNewProc(const char* name, ULONG pri, struct MsgPort* port, ULONG stackSize, APTR initPC, APTR finalPC) {
    // ... (código de la función - Ver Mensaje 00886)
}

// Finaliza la ejecución de UAE60
void uae60_Exit(LONG returnCode) {
    // ... (código de la función - Ver Mensaje 00886)
}

// Abre una librería
struct Library* uae60_OpenLibrary(const char* libName, ULONG version) {
    // ... (código de la función - Ver Mensaje 00886)
}

// Cierra una librería
void uae60_CloseLibrary(struct Library* library) {
    // ... (código de la función - Ver Mensaje 00886)
}

// Suma una librería (no se usa en AROS x86)
void uae60_SumLibrary(struct Library* library) {
    // ... (código de la función - Ver Mensaje 00886)
}

// Deshabilita la multitarea.
void uae60_Forbid() {
    // ... (código de la función - Ver Mensaje 00995)
}

// Reanuda la multitarea.
void uae60_Permit() {
    // ... (código de la función - Ver Mensaje 00995)
}

// Establece la prioridad de una tarea (si no se especifica, se usa la tarea actual).
ULONG uae60_SetTaskPri(struct Task* task, LONG pri) {
    // ... (código de la función - Ver Mensaje 00995)
}

// Suspende la ejecución durante un tiempo determinado.
void uae60_Delay(ULONG unit) {
    // ... (código de la función - Ver Mensaje 00995)
}

// Función para ejecutar una instrucción 68060
void uae60_execute_instruction(uint16_t opcode) {
    // ... (código de la función - Ver Mensaje 00732)
}

