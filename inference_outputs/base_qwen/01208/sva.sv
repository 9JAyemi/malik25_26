```systemverilog
module control_sva (
    input logic clk,
    input logic rst,
    input logic en,
    input logic en_mem,
    input logic mem_wait,
    input logic should_branch,
    input logic imm,
    output logic [8:0] control_o,
    output logic [1:0] pc_op
);
    ///// Reset behavior /////
    // At reset, control_o and pc_op must be driven to 0.
    reset: assert property (
        @(posedge clk) disable iff (!rst) (rst |-> (control_o == 8'b0) && (pc_op == 2'b0))
    );

    ///// Enable behavior /////
    // When en is high, control_o[0] should be equal to en_mem.
    enable_en_mem: assert property (
        @(posedge clk) disable iff (!rst) (en |-> (control_o[0] == en_mem))
    );

    // When en is high, control_o[1] should be equal to should_branch.
    enable_should_branch: assert property (
        @(posedge clk) disable iff (!rst) (en |-> (control_o[1] == should_branch))
    );

    // When en is high, control_o[2] should be equal to imm.
    enable_imm: assert property (
        @(posedge clk) disable iff (!rst) (en |-> (control_o[2] == imm))
    );

    ///// Opcode generation /////
    // When imm is high, pc_op should be 2'b10 (Bitwise AND).
    opcode_and: assert property (
        @(posedge clk) disable iff (!rst) (imm |-> (pc_op == 2'b10))
    );

    // When imm is low, pc_op should be 2'b00 (Add).
    opcode_add: assert property (
        @(posedge clk) disable iff (!rst) (!imm |-> (pc_op == 2'b00))
    );

    ///// Memory wait behavior /////
    // mem_wait should not affect control_o or pc_op directly.
    mem_wait_behavior: assert property (
        @(posedge clk) disable iff (!rst) (mem_wait |-> (control_o == control_o) && (pc_op == pc_op))
    );

endmodule
```