module ID_EX_sva (
    input logic clk,
    input logic rst,
    input logic BJ,
    input logic [31:0] id_a,
    input logic [31:0] id_b,
    input logic [31:0] id_d2,
    input logic [31:0] id_instr,
    input logic [4:0]  id_td,
    input logic [4:0]  id_Aluc,
    input logic        id_WREG,
    input logic        id_WMEM,
    input logic        id_LW,
    input logic [31:0] ex_a,
    input logic [31:0] ex_b,
    input logic [31:0] ex_d2,
    input logic [31:0] ex_instr,
    input logic [4:0]  ex_td,
    input logic [4:0]  ex_Aluc,
    input logic        ex_WREG,
    input logic        ex_WMEM,
    input logic        ex_LW
);
    ///// Reset behavior /////
    // During reset, all EX regs are 0 and ex_instr is 32'b100000.
    check_reset_defaults: assert property (
        @(posedge clk) rst |-> (ex_a==32'b0 && ex_b==32'b0 && ex_d2==32'b0 &&
                                ex_td==5'b0 && ex_Aluc==5'b0 &&
                                ex_WREG==1'b0 && ex_WMEM==1'b0 && ex_LW==1'b0 &&
                                ex_instr==32'b100000)
    );

    ///// Flush behavior (BJ) /////
    // If BJ is asserted, next cycle EX regs clear to 0 and ex_instr to 32'b100000.
    check_flush_clears_outputs: assert property (
        @(posedge clk) disable iff (rst)
            BJ |=> (ex_a==32'b0 && ex_b==32'b0 && ex_d2==32'b0 &&
                    ex_td==5'b0 && ex_Aluc==5'b0 &&
                    ex_WREG==1'b0 && ex_WMEM==1'b0 && ex_LW==1'b0 &&
                    ex_instr==32'b100000)
    );

    ///// Pass-through behavior when not flushing /////
    // When BJ is 0, ex_a captures id_a in the next cycle.
    check_pass_through_ex_a: assert property (
        @(posedge clk) disable iff (rst) (!BJ) |=> (ex_a == $past(id_a))
    );
    // When BJ is 0, ex_b captures id_b in the next cycle.
    check_pass_through_ex_b: assert property (
        @(posedge clk) disable iff (rst) (!BJ) |=> (ex_b == $past(id_b))
    );
    // When BJ is 0, ex_d2 captures id_d2 in the next cycle.
    check_pass_through_ex_d2: assert property (
        @(posedge clk) disable iff (rst) (!BJ) |=> (ex_d2 == $past(id_d2))
    );
    // When BJ is 0, ex_td captures id_td in the next cycle.
    check_pass_through_ex_td: assert property (
        @(posedge clk) disable iff (rst) (!BJ) |=> (ex_td == $past(id_td))
    );
    // When BJ is 0, ex_Aluc captures id_Aluc in the next cycle.
    check_pass_through_ex_Aluc: assert property (
        @(posedge clk) disable iff (rst) (!BJ) |=> (ex_Aluc == $past(id_Aluc))
    );
    // When BJ is 0, ex_WREG captures id_WREG in the next cycle.
    check_pass_through_ex_WREG: assert property (
        @(posedge clk) disable iff (rst) (!BJ) |=> (ex_WREG == $past(id_WREG))
    );
    // When BJ is 0, ex_WMEM captures id_WMEM in the next cycle.
    check_pass_through_ex_WMEM: assert property (
        @(posedge clk) disable iff (rst) (!BJ) |=> (ex_WMEM == $past(id_WMEM))
    );
    // When BJ is 0, ex_LW captures id_LW in the next cycle.
    check_pass_through_ex_LW: assert property (
        @(posedge clk) disable iff (rst) (!BJ) |=> (ex_LW == $past(id_LW))
    );
    // When BJ is 0, ex_instr captures id_instr in the next cycle.
    check_pass_through_ex_instr: assert property (
        @(posedge clk) disable iff (rst) (!BJ) |=> (ex_instr == $past(id_instr))
    );
endmodule