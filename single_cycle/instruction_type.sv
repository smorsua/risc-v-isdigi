`ifndef INSTRUCTION_TYPE_GUARD
`define INSTRUCTION_TYPE_GUARD
typedef enum {
    R_FORMAT    = 'b0110011,
    I_FORMAT    = 'b0010011,
    S_FORMAT    = 'b0100011,
    B_FORMAT    = 'b1100011,
    AUIPC       = 'b0010111,
    LUI         = 'b0110111
    /*J_FORMAT = 'b1101111*/
} instruction_type;
`endif // INSTRUCTION_TYPE_GUARD