module mux_2_1_sva (
    input logic a,
    input logic b,
    input logic sel,
    output logic out
);
    // Mux output should be equal to a when sel is 0
    mux_0: assert property (
        @(posedge clk) disable iff (!reset_n) (sel == 1'b0) |-> (out == a)
    );
    // Mux output should be equal to b when sel is 1
    mux_1: assert property (
        @(posedge clk) disable iff (!reset_n) (sel == 1'b1) |-> (out == b)
    );
endmodule