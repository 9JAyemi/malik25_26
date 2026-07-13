module Forwarding_sva (
    input logic clk,
    input logic [4:0] EX_rs,
    input logic [4:0] EX_rt,
    input logic [4:0] MEM_rd,
    input logic [4:0] WB_rd,
    input logic MEM_RegWrite,
    input logic WB_RegWrite,
    input logic [1:0] ForwardA,
    input logic [1:0] ForwardB
);

    // ForwardA selects WB forwarding when the WB condition is taken.
    check_forwarda_wb_select: assert property (
        @(posedge clk)
        ((WB_RegWrite && WB_rd && (WB_rd == EX_rs) &&
          ((MEM_rd != EX_rs) || (~MEM_RegWrite))) === 1'b1)
        |-> (ForwardA == 2'b01)
    );

    // ForwardA selects MEM forwarding when WB is not taken and the MEM condition is taken.
    check_forwarda_mem_select: assert property (
        @(posedge clk)
        (((WB_RegWrite && WB_rd && (WB_rd == EX_rs) &&
           ((MEM_rd != EX_rs) || (~MEM_RegWrite))) !== 1'b1) &&
         ((MEM_RegWrite && MEM_rd && (MEM_rd == EX_rs)) === 1'b1))
        |-> (ForwardA == 2'b10)
    );

    // ForwardA is zero when neither forwarding condition is taken.
    check_forwarda_default_zero: assert property (
        @(posedge clk)
        (((WB_RegWrite && WB_rd && (WB_rd == EX_rs) &&
           ((MEM_rd != EX_rs) || (~MEM_RegWrite))) !== 1'b1) &&
         ((MEM_RegWrite && MEM_rd && (MEM_rd == EX_rs)) !== 1'b1))
        |-> (ForwardA == 2'b00)
    );

    // ForwardA gives MEM priority when both MEM and WB match EX_rs.
    check_forwarda_mem_priority: assert property (
        @(posedge clk)
        (((MEM_RegWrite && MEM_rd && (MEM_rd == EX_rs)) === 1'b1) &&
         ((WB_RegWrite && WB_rd && (WB_rd == EX_rs)) === 1'b1))
        |-> (ForwardA == 2'b10)
    );

    // ForwardA only uses implemented encodings.
    check_forwarda_valid_encoding: assert property (
        @(posedge clk)
        (ForwardA inside {2'b00, 2'b01, 2'b10})
    );

    // ForwardB selects WB forwarding when the WB condition is taken.
    check_forwardb_wb_select: assert property (
        @(posedge clk)
        ((WB_RegWrite && WB_rd && (WB_rd == EX_rt) &&
          ((MEM_rd != EX_rt) || (~MEM_RegWrite))) === 1'b1)
        |-> (ForwardB == 2'b01)
    );

    // ForwardB selects MEM forwarding when WB is not taken and the MEM condition is taken.
    check_forwardb_mem_select: assert property (
        @(posedge clk)
        (((WB_RegWrite && WB_rd && (WB_rd == EX_rt) &&
           ((MEM_rd != EX_rt) || (~MEM_RegWrite))) !== 1'b1) &&
         ((MEM_RegWrite && MEM_rd && (MEM_rd == EX_rt)) === 1'b1))
        |-> (ForwardB == 2'b10)
    );

    // ForwardB is zero when neither forwarding condition is taken.
    check_forwardb_default_zero: assert property (
        @(posedge clk)
        (((WB_RegWrite && WB_rd && (WB_rd == EX_rt) &&
           ((MEM_rd != EX_rt) || (~MEM_RegWrite))) !== 1'b1) &&
         ((MEM_RegWrite && MEM_rd && (MEM_rd == EX_rt)) !== 1'b1))
        |-> (ForwardB == 2'b00)
    );

    // ForwardB gives MEM priority when both MEM and WB match EX_rt.
    check_forwardb_mem_priority: assert property (
        @(posedge clk)
        (((MEM_RegWrite && MEM_rd && (MEM_rd == EX_rt)) === 1'b1) &&
         ((WB_RegWrite && WB_rd && (WB_rd == EX_rt)) === 1'b1))
        |-> (ForwardB == 2'b10)
    );

    // ForwardB only uses implemented encodings.
    check_forwardb_valid_encoding: assert property (
        @(posedge clk)
        (ForwardB inside {2'b00, 2'b01, 2'b10})
    );

endmodule