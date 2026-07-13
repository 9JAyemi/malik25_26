module mux4_sva (
    input logic       clk,
    input logic       reset,
    input logic [1:0] select,
    input logic [3:0] sig_in,
    input logic       sig_out
);

    // A reset on the previous clock clears the registered output.
    check_reset_clears_output: assert property (
        @(posedge clk) disable iff (reset)
        $past(reset) |-> (sig_out == 1'b0)
    );

    // When select was 00, the output reflects sig_in[0] from the previous clock.
    check_select_00_routes_sig_in0: assert property (
        @(posedge clk) disable iff (reset)
        ($past(reset) == 1'b0 && $past(select) == 2'b00) |-> (sig_out == $past(sig_in[0]))
    );

    // When select was 01, the output reflects sig_in[1] from the previous clock.
    check_select_01_routes_sig_in1: assert property (
        @(posedge clk) disable iff (reset)
        ($past(reset) == 1'b0 && $past(select) == 2'b01) |-> (sig_out == $past(sig_in[1]))
    );

    // When select was 10, the output reflects sig_in[2] from the previous clock.
    check_select_10_routes_sig_in2: assert property (
        @(posedge clk) disable iff (reset)
        ($past(reset) == 1'b0 && $past(select) == 2'b10) |-> (sig_out == $past(sig_in[2]))
    );

    // When select was 11, the output reflects sig_in[3] from the previous clock.
    check_select_11_routes_sig_in3: assert property (
        @(posedge clk) disable iff (reset)
        ($past(reset) == 1'b0 && $past(select) == 2'b11) |-> (sig_out == $past(sig_in[3]))
    );

endmodule