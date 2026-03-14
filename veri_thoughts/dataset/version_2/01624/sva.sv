module ID_EX_sva (
    input logic clk,
    input logic rst,
    input logic [31:0] id_a,
    input logic [31:0] id_b,
    input logic [4:0]  id_td,
    input logic [31:0] id_d2,
    input logic [4:0]  id_Aluc,
    input logic        id_WREG,
    input logic        id_WMEM,
    input logic        id_LW,
    input logic [31:0] id_instr,
    input logic [31:0] ex_a,
    input logic [31:0] ex_b,
    input logic [4:0]  ex_td,
    input logic [31:0] ex_d2,
    input logic [4:0]  ex_Aluc,
    input logic        ex_WREG,
    input logic        ex_WMEM,
    input logic        ex_LW,
    input logic [31:0] ex_instr
);
    // Clock: clk; Reset: rst (active-high async). Sequential pipeline register with async reset. Pass-through of id_* to ex_* on each clk when rst==0.

    ///// Reset behavior /////
    // While reset is asserted, outputs hold their reset values.
    reset_values_all: assert property (
        @(posedge clk) rst |-> (ex_a == 32'b0) && (ex_b == 32'b0) && (ex_d2 == 32'b0) &&
                               (ex_td == 5'b0) && (ex_Aluc == 5'b0) &&
                               (ex_WREG == 1'b0) && (ex_WMEM == 1'b0) && (ex_LW == 1'b0) &&
                               (ex_instr == 32'b100000)
    );

    ///// Pipeline pass-through (one-cycle latency) /////
    // ex_a updates to prior-cycle id_a when out of reset.
    pipe_ex_a: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst)) |-> (ex_a == $past(id_a))
    );
    // ex_b updates to prior-cycle id_b when out of reset.
    pipe_ex_b: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst)) |-> (ex_b == $past(id_b))
    );
    // ex_d2 updates to prior-cycle id_d2 when out of reset.
    pipe_ex_d2: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst)) |-> (ex_d2 == $past(id_d2))
    );
    // ex_td updates to prior-cycle id_td when out of reset.
    pipe_ex_td: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst)) |-> (ex_td == $past(id_td))
    );
    // ex_Aluc updates to prior-cycle id_Aluc when out of reset.
    pipe_ex_Aluc: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst)) |-> (ex_Aluc == $past(id_Aluc))
    );
    // ex_WREG updates to prior-cycle id_WREG when out of reset.
    pipe_ex_WREG: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst)) |-> (ex_WREG == $past(id_WREG))
    );
    // ex_WMEM updates to prior-cycle id_WMEM when out of reset.
    pipe_ex_WMEM: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst)) |-> (ex_WMEM == $past(id_WMEM))
    );
    // ex_LW updates to prior-cycle id_LW when out of reset.
    pipe_ex_LW: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst)) |-> (ex_LW == $past(id_LW))
    );
    // ex_instr updates to prior-cycle id_instr when out of reset.
    pipe_ex_instr: assert property (
        @(posedge clk) disable iff (rst) (!$past(rst)) |-> (ex_instr == $past(id_instr))
    );

endmodule