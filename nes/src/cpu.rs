use crate::opcodes;
use std::collections::HashMap;

bitflags! {
    /// # Status Register (P) http://wiki.nesdev.com/w/index.php/Status_flags
    ///
    ///  7 6 5 4 3 2 1 0
    ///  N V _ B D I Z C
    ///  | |   | | | | +--- Carry Flag
    ///  | |   | | | +----- Zero Flag
    ///  | |   | | +------- Interrupt Disable
    ///  | |   | +--------- Decimal Mode (not used on NES)
    ///  | |   +----------- Break Command
    ///  | +--------------- Overflow Flag
    ///  +----------------- Negative Flag
    ///
    pub struct CpuFlags: u8 {
        const CARRY             = 0b00000001;
        const ZERO              = 0b00000010;
        const INTERRUPT_DISABLE = 0b00000100;
        const DECIMAL_MODE      = 0b00001000;
        const BREAK             = 0b00010000;
        const BREAK2            = 0b00100000;
        const OVERFLOW          = 0b01000000;
        const NEGATIV           = 0b10000000;
    }
}

const STACK: u16 = 0x0100;
const STACK_RESET: u8 = 0xfd;

pub struct CPU {
    pub register_a: u8,
    pub register_x: u8,
    pub register_y: u8,
    pub status: u8,
    pub program_counter: u16,
    pub stack_pointer: u8,
    memory: [u8; 0xFFFF],
}

#[derive(Debug)]
#[allow(non_camel_case_types)]
pub enum AddressingMode {
    Immediate,
    ZeroPage,
    ZeroPage_X,
    ZeroPage_Y,
    Absolute,
    Absolute_X,
    Absolute_Y,
    Indirect_X,
    Indirect_Y,
    NoneAddressing,
}

trait Mem {
    fn mem_read(&self, addr: u16) -> u8;

    fn mem_write(&mut self, addr: u16, data: u8);

    fn mem_read_u16(&self, pos: u16) -> u16 {
        let lo = self.mem_read(pos) as u16;
        let hi = self.mem_read(pos + 1) as u16;
        (hi << 8) | (lo as u16)
    }

    fn mem_write_u16(&mut self, pos: u16, data: u16) {
        let hi = (data >> 8) as u8;
        let lo = (data & 0xff) as u8;
        self.mem_write(pos, lo);
        self.mem_write(pos + 1, hi);
    }
}

impl Mem for CPU {
    fn mem_read(&self, addr: u16) -> u8 {
        self.memory[addr as usize]
    }

    fn mem_write(&mut self, addr: u16, data: u8) {
        self.memory[addr as usize] = data;
    }
}

impl CPU {
    pub fn new() -> Self {}

    fn get_operand_address(&self, mode: &AddressingMode) -> u16 {}

    fn ldy(&mut self, mode: &AddressingMode) {}

    fn ldx(&mut self, mode: &AddressingMode) {}

    fn lda(&mut self, mode: &AddressingMode) {}

    fn sta(&mut self, mode: &AddressingMode) {}

    fn set_register_a(&mut self, value: u8) {}

    fn and(&mut self, mode: &AddressingMode) {}

    fn eor(&mut self, mode: AddressingMode) {}

    fn ora(&mut self, mode: &AddressingMode) {}

    fn tax(&mut self) {}

    fn update_zero_and_negative_flags(&mut self, result: u8) {}

    fn inx(&mut self) {}

    fn iny(&mut self) {}

    pub fn load_and_run(&mut self, program: Vec<u8>) {}

    pub fn load(&mut self, program: Vec<u8>) {}

    pub fn reset(&mut self) {}

    fn set_carry_flag(&mut self) {}

    fn clear_carry_flag(&mut self) {}

    // note: ignoring decimal mode
    fn add_to_register_a(&mut self, data: u8) {}

    fn sbc(&mut self, mode: &AddressingMode) {}

    fn adc(&mut self, mode: &AddressingMode) {}

    fn stack_pop(&mut self) -> u8 {}

    fn stack_push(&mut self, data: u8) {}

    fn stack_push_u16(&mut self, data: u16) {}

    fn stack_pop_u16(&mut self) {}

    fn asl_accumulator(&mut self) {}

    fn asl(&mut self, mode: &AddressingMode) -> u8 {}

    fn lsr_accumulator(&mut self) {}

    fn lsr(&mut self, mode: &AddressingMode) -> u8 {}

    fn rol(&mut self, mode: &AddressingMode) -> u8 {}

    fn rol_accumulator(&mut self) {}

    fn ror(&mut self, mode: &AddressingMode) -> u8 {}

    fn ror_accumulator(&mut self) {}

    fn inc(&mut self, mode: &AddressingMode) -> u8 {}

    fn dey(&mut self) {}

    fn dex(&mut self) {}

    fn dec(&mut self, mode: &AddressingMode) -> u8 {}

    fn pla(&mut self) {}

    fn plp(&mut self) {}

    fn php(&mut self) {}

    fn bit(&mut self, mode: &AddressingMode) {}

    fn compare(&mut self, mode: &AddressingMode, compare_with: u8) {}

    fn branch(&mut self, condition: bool) {}

    pub fn run(&mut self) {}
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_0xa9_lda_immidiate_load_data() {
        let mut cpu = CPU::new();
        cpu.interpret(vec![0xa9, 0x05, 0x00]);
        assert_eq!(cpu.register_a, 0x05);
        assert!(cpu.status & 0b0000_0010 == 0b00);
        assert!(cpu.status & 0b1000_0000 == 0);
    }

    #[test]
    fn test_0xa9_lda_zero_flag() {
        let mut cpu = CPU::new();
        cpu.interpret(vec![0xa9, 0x00, 0x00]);
        assert!(cpu.status & 0b0000_0010 == 0b10);
    }

    #[test]
    fn test_0xaa_tax_move_a_to_x() {
        let mut cpu = CPU::new();
        cpu.register_a = 10;
        cpu.interpret(vec![0xaa, 0x00]);

        assert_eq!(cpu.register_x, 10)
    }

    #[test]
    fn test_5_ops_working_together() {
        let mut cpu = CPU::new();
        cpu.interpret(vec![0xa9, 0xc0, 0xaa, 0xe8, 0x00]);

        assert_eq!(cpu.register_x, 0xc1)
    }

    #[test]
    fn test_inx_overflow() {
        let mut cpu = CPU::new();
        cpu.register_x = 0xff;
        cpu.interpret(vec![0xe8, 0xe8, 0x00]);

        assert_eq!(cpu.register_x, 1)
    }
}
