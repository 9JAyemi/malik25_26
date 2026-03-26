module forwarding_unit_sva (
    input logic [4:0] rt_addr_IDEX,
    input logic [4:0] rs_addr_IDEX,
    input logic [4:0] rd_addr_EXMEM,
    input logic [4:0] rd_addr_MEMWB,
    input logic regwrite_EXMEM,
    input logic regwrite_MEMWB,
    input logic [1:0] forwardA,
    input logic [1:0] forwardB
);

    wire rs_from_mem, rt_from_mem, rs_from_ex, rt_from_ex;

    assign rs_from_mem = (rd_addr_MEMWB == rs_addr_IDEX) && (regwrite_MEMWB == 1'b1);
    assign rt_from_mem = (rd_addr_MEMWB == rt_addr_IDEX) && (regwrite_MEMWB == 1'b1);
    assign rs_from_ex  = (rd_addr_EXMEM == rs_addr_IDEX) && (regwrite_EXMEM == 1'b1);
    assign rt_from_ex  = (rd_addr_EXMEM == rt_addr_IDEX) && (regwrite_EXMEM == 1'b1);

    // forwardA must match the implemented rs forwarding equation.
    check_forwardA_equation: assert property (
        @($global_clock) forwardA == ((rs_from_mem | rs_from_ex) ? 2'b10 : 2'b00)
    );

    // forwardB must match the implemented rt forwarding equation.
    check_forwardB_equation: assert property (
        @($global_clock) forwardB == ((rt_from_mem | rt_from_ex) ? 2'b10 : 2'b00)
    );

    // forwardA uses only the encodings produced by the RTL.
    check_forwardA_valid_encoding: assert property (
        @($global_clock) (forwardA == 2'b00) || (forwardA == 2'b10)
    );

    // forwardB uses only the encodings produced by the RTL.
    check_forwardB_valid_encoding: assert property (
        @($global_clock) (forwardB == 2'b00) || (forwardB == 2'b10)
    );

    // An EX/MEM rs match with write enable must drive forwardA active.
    check_forwardA_exmem_match_sets_forward: assert property (
        @($global_clock) rs_from_ex |-> (forwardA == 2'b10)
    );

    // A MEM/WB rs match with write enable must drive forwardA active.
    check_forwardA_memwb_match_sets_forward: assert property (
        @($global_clock) rs_from_mem |-> (forwardA == 2'b10)
    );

    // With no rs match from either stage, forwardA must be inactive.
    check_forwardA_no_match_clears_forward: assert property (
        @($global_clock) !(rs_from_mem | rs_from_ex) |-> (forwardA == 2'b00)
    );

    // An EX/MEM rt match with write enable must drive forwardB active.
    check_forwardB_exmem_match_sets_forward: assert property (
        @($global_clock) rt_from_ex |-> (forwardB == 2'b10)
    );

    // A MEM/WB rt match with write enable must drive forwardB active.
    check_forwardB_memwb_match_sets_forward: assert property (
        @($global_clock) rt_from_mem |-> (forwardB == 2'b10)
    );

    // With no rt match from either stage, forwardB must be inactive.
    check_forwardB_no_match_clears_forward: assert property (
        @($global_clock) !(rt_from_mem | rt_from_ex) |-> (forwardB == 2'b00)
    );

endmodule