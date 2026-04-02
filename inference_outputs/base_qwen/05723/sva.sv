module mux_add_sub_sva (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic select_ctrl,
    input logic add_sub_ctrl,
    output logic [3:0] Q
);
    // No clock or reset signals are present in the RTL

    // The logic is purely combinational

    // The adder/subtractor output is correctly assigned based on the add_sub_ctrl signal
    adder_subtractor_output: assert property (
        @(posedge clk) disable iff (!RESETn) (add_sub_ctrl ? (a + b) : (a - b)) == add_sub_out
    );

    // The multiplexer output is correctly assigned based on the mux_enable signal
    multiplexer_output: assert property (
        @(posedge clk) disable iff (!RESETn) (mux_enable ? add_sub_out[3:0] : 4'h0) == Q
    );

    // The mux_enable signal is correctly assigned based on the add_sub_ctrl signal
    mux_enable_assignment: assert property (
        @(posedge clk) disable iff (!RESETn) add_sub_ctrl == mux_enable
    );
endmodule