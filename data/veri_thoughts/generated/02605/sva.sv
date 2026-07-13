module FORWARD_sva (
    input logic clk,
    input logic [4:0] Rs_ID_EX,
    input logic [4:0] Rt_ID_EX,
    input logic [4:0] Rd_EX_MEM,
    input logic [4:0] Rs_IF_ID,
    input logic [4:0] Rt_IF_ID,
    input logic [4:0] Rd_MEM_REG,
    input logic RegWrite_EX_MEM,
    input logic RegWrite_MEM_REG,
    input logic [3:0] Rd_write_byte_en,
    input logic loaduse,
    input logic [3:0] RsOut_sel,
    input logic [3:0] RtOut_sel,
    input logic [7:0] A_in_sel,
    input logic [7:0] B_in_sel
);
    // RsOut_sel equals Rd_write_byte_en when MEM_REG writes to Rs_IF_ID and no load-use
    check_rsout_sel_set_on_match: assert property (
        @(posedge clk) (!loaduse && RegWrite_MEM_REG && (Rd_MEM_REG == Rs_IF_ID)) |-> (RsOut_sel == Rd_write_byte_en)
    );

    // RsOut_sel is zero otherwise
    check_rsout_sel_zero_else: assert property (
        @(posedge clk) !( !loaduse && RegWrite_MEM_REG && (Rd_MEM_REG == Rs_IF_ID) ) |-> (RsOut_sel == 4'b0000)
    );

    // RtOut_sel equals Rd_write_byte_en when MEM_REG writes to Rt_IF_ID and no load-use
    check_rtout_sel_set_on_match: assert property (
        @(posedge clk) (!loaduse && RegWrite_MEM_REG && (Rd_MEM_REG == Rt_IF_ID)) |-> (RtOut_sel == Rd_write_byte_en)
    );

    // RtOut_sel is zero otherwise
    check_rtout_sel_zero_else: assert property (
        @(posedge clk) !( !loaduse && RegWrite_MEM_REG && (Rd_MEM_REG == Rt_IF_ID) ) |-> (RtOut_sel == 4'b0000)
    );

    // A_in_sel is 0x55 when EX_MEM writes to Rs_ID_EX (priority case)
    check_a_in_sel_exmem_priority: assert property (
        @(posedge clk) (RegWrite_EX_MEM && (Rd_EX_MEM == Rs_ID_EX)) |-> (A_in_sel == 8'b01010101)
    );

    // A_in_sel maps from MEM_REG byte enables when EX_MEM does not match and MEM_REG matches Rs_ID_EX
    check_a_in_sel_memreg_map: assert property (
        @(posedge clk)
        ((!RegWrite_EX_MEM || (Rd_EX_MEM != Rs_ID_EX)) && RegWrite_MEM_REG && (Rd_MEM_REG == Rs_ID_EX)) |->
        ( (A_in_sel[7:6] == (Rd_write_byte_en[3] ? 2'b10 : 2'b00)) &&
          (A_in_sel[5:4] == (Rd_write_byte_en[2] ? 2'b10 : 2'b00)) &&
          (A_in_sel[3:2] == (Rd_write_byte_en[1] ? 2'b10 : 2'b00)) &&
          (A_in_sel[1:0] == 2'b10) )
    );

    // A_in_sel is zero when neither EX_MEM nor MEM_REG matches Rs_ID_EX
    check_a_in_sel_zero_else: assert property (
        @(posedge clk)
        !( (RegWrite_EX_MEM && (Rd_EX_MEM == Rs_ID_EX)) || (RegWrite_MEM_REG && (Rd_MEM_REG == Rs_ID_EX)) ) |-> (A_in_sel == 8'b00000000)
    );

    // B_in_sel is 0x55 when EX_MEM writes to Rt_ID_EX (priority case)
    check_b_in_sel_exmem_priority: assert property (
        @(posedge clk) (RegWrite_EX_MEM && (Rd_EX_MEM == Rt_ID_EX)) |-> (B_in_sel == 8'b01010101)
    );

    // B_in_sel maps from MEM_REG byte enables when EX_MEM does not match and MEM_REG matches Rt_ID_EX
    check_b_in_sel_memreg_map: assert property (
        @(posedge clk)
        ((!RegWrite_EX_MEM || (Rd_EX_MEM != Rt_ID_EX)) && RegWrite_MEM_REG && (Rd_MEM_REG == Rt_ID_EX)) |->
        ( (B_in_sel[7:6] == (Rd_write_byte_en[3] ? 2'b10 : 2'b00)) &&
          (B_in_sel[5:4] == (Rd_write_byte_en[2] ? 2'b10 : 2'b00)) &&
          (B_in_sel[3:2] == (Rd_write_byte_en[1] ? 2'b10 : 2'b00)) &&
          (B_in_sel[1:0] == (Rd_write_byte_en[0] ? 2'b10 : 2'b00)) )
    );

    // B_in_sel is zero when neither EX_MEM nor MEM_REG matches Rt_ID_EX
    check_b_in_sel_zero_else: assert property (
        @(posedge clk)
        !( (RegWrite_EX_MEM && (Rd_EX_MEM == Rt_ID_EX)) || (RegWrite_MEM_REG && (Rd_MEM_REG == Rt_ID_EX)) ) |-> (B_in_sel == 8'b00000000)
    );
endmodule