`ifndef INSTRUCTION_TYPE_GUARD
`define INSTRUCTION_TYPE_GUARD
typedef enum logic [6:0] {
    R_FORMAT    = 7'b011x011,
    I_FORMAT    = 7'b00xx011,
    S_FORMAT    = 7'b0100011,
    B_FORMAT    = 7'b1100011,
    U_FORMAT    = 7'b0x10111,
    J_FORMAT    = 7'b110x111
} instruction_type;
`endif // INSTRUCTION_TYPE_GUARD

