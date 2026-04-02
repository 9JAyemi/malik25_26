module mux2_sva (
    input wire clk,
    input wire sel,
    input wire in1,
    input wire in2,
    output reg out
);
    // Mux output should be equal to in1 when sel is 0
    mux_out_when_sel_0: assert property (
        @(posedge clk) disable iff (!clk) (sel == 1'b0) |-> (out == in1)
    );

    // Mux output should be equal to in2 when sel is 1
    mux_out_when_sel_1: assert property (
        @(posedge clk) disable iff (!clk) (sel == 1'b1) |-> (out == in2)
    );
endmodule