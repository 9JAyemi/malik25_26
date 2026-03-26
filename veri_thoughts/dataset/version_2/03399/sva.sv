module forward_mem_stage_sva (
    input logic [2:0] mem_wb_regA,
    input logic [2:0] mem_wb_regC,
    input logic [2:0] ex_mem_regA,
    input logic [5:0] mem_wb_op,
    input logic [5:0] ex_mem_op,
    input logic       mem_wb_CCR_write,
    input logic       ex_mem_CCR_write,
    input logic [1:0] F3
);

    localparam [5:0] ADD = 6'b000000;
    localparam [5:0] NDU = 6'b001000;
    localparam [5:0] ADC = 6'b000010;
    localparam [5:0] ADZ = 6'b000001;
    localparam [5:0] NDC = 6'b001010;
    localparam [5:0] NDZ = 6'b001001;
    localparam [3:0] LW  = 4'b0100;
    localparam [3:0] SW  = 4'b0101;

    // Combinational RTL with no explicit clock or reset; sample on the global clock.

    // F3 only takes values driven by the RTL: 0, 2, or 3.
    check_f3_encoding: assert property (
        @($global_clock)
        ((F3 == 2'b00) || (F3 == 2'd2) || (F3 == 2'd3))
    );

    // Non-store ex_mem operations force no forwarding.
    check_non_store_zero: assert property (
        @($global_clock)
        (ex_mem_op[5:2] != SW) |-> (F3 == 2'b00)
    );

    // A store with matching mem_wb_regC and a supported ALU op forwards code 2 when CCR write is low.
    check_store_alu_match_forward: assert property (
        @($global_clock)
        ((ex_mem_op[5:2] == SW) &&
         (ex_mem_regA == mem_wb_regC) &&
         ((mem_wb_op == ADD) || (mem_wb_op == NDU) || (mem_wb_op == ADC) ||
          (mem_wb_op == ADZ) || (mem_wb_op == NDC) || (mem_wb_op == NDZ)) &&
         (mem_wb_CCR_write == 1'b0))
        |-> (F3 == 2'd2)
    );

    // A store with matching mem_wb_regA and a load in mem_wb forwards code 3.
    check_store_load_match_forward: assert property (
        @($global_clock)
        ((ex_mem_op[5:2] == SW) &&
         (ex_mem_regA == mem_wb_regA) &&
         (mem_wb_op[5:2] == LW))
        |-> (F3 == 2'd3)
    );

    // A store with neither forwarding condition active drives F3 to zero.
    check_store_no_match_zero: assert property (
        @($global_clock)
        ((ex_mem_op[5:2] == SW) &&
         !((ex_mem_regA == mem_wb_regC) &&
           ((mem_wb_op == ADD) || (mem_wb_op == NDU) || (mem_wb_op == ADC) ||
            (mem_wb_op == ADZ) || (mem_wb_op == NDC) || (mem_wb_op == NDZ)) &&
           (mem_wb_CCR_write == 1'b0)) &&
         !((ex_mem_regA == mem_wb_regA) &&
           (mem_wb_op[5:2] == LW)))
        |-> (F3 == 2'b00)
    );

    // F3 value 2 only comes from the ALU-result forwarding case.
    check_f3_two_only_on_alu_forward: assert property (
        @($global_clock)
        (F3 == 2'd2) |-> ((ex_mem_op[5:2] == SW) &&
                          (ex_mem_regA == mem_wb_regC) &&
                          ((mem_wb_op == ADD) || (mem_wb_op == NDU) || (mem_wb_op == ADC) ||
                           (mem_wb_op == ADZ) || (mem_wb_op == NDC) || (mem_wb_op == NDZ)) &&
                          (mem_wb_CCR_write == 1'b0))
    );

    // F3 value 3 only comes from the load-result forwarding case.
    check_f3_three_only_on_load_forward: assert property (
        @($global_clock)
        (F3 == 2'd3) |-> ((ex_mem_op[5:2] == SW) &&
                          (ex_mem_regA == mem_wb_regA) &&
                          (mem_wb_op[5:2] == LW))
    );

    // A matching ALU op does not forward when mem_wb_CCR_write is high.
    check_ccr_write_blocks_alu_forward: assert property (
        @($global_clock)
        ((ex_mem_op[5:2] == SW) &&
         (ex_mem_regA == mem_wb_regC) &&
         ((mem_wb_op == ADD) || (mem_wb_op == NDU) || (mem_wb_op == ADC) ||
          (mem_wb_op == ADZ) || (mem_wb_op == NDC) || (mem_wb_op == NDZ)) &&
         (mem_wb_CCR_write == 1'b1))
        |-> (F3 == 2'b00)
    );

    // F3 is zero only when the ex_mem op is not a store or both forwarding conditions are false.
    check_f3_zero_only_without_forward_condition: assert property (
        @($global_clock)
        (F3 == 2'b00) |-> ((ex_mem_op[5:2] != SW) ||
                           (!((ex_mem_regA == mem_wb_regC) &&
                              ((mem_wb_op == ADD) || (mem_wb_op == NDU) || (mem_wb_op == ADC) ||
                               (mem_wb_op == ADZ) || (mem_wb_op == NDC) || (mem_wb_op == NDZ)) &&
                              (mem_wb_CCR_write == 1'b0)) &&
                            !((ex_mem_regA == mem_wb_regA) &&
                              (mem_wb_op[5:2] == LW))))
    );

endmodule