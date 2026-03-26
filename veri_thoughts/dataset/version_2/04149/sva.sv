module mux_4to1_enable_sva (
    input logic [3:0] in,
    input logic [1:0] sel,
    input logic enable,
    input logic out
);

    // Output matches the RTL equation.
    check_output_matches_mux_equation: assert property (
        @($global_clock) out == (enable & in[sel])
    );

    // When disabled, the output is low.
    check_disable_forces_low: assert property (
        @($global_clock) (!enable) |-> (out == 1'b0)
    );

    // With sel=0 and enable high, output follows in[0].
    check_sel_0_routes_in0: assert property (
        @($global_clock) (enable && (sel == 2'b00)) |-> (out == in[0])
    );

    // With sel=1 and enable high, output follows in[1].
    check_sel_1_routes_in1: assert property (
        @($global_clock) (enable && (sel == 2'b01)) |-> (out == in[1])
    );

    // With sel=2 and enable high, output follows in[2].
    check_sel_2_routes_in2: assert property (
        @($global_clock) (enable && (sel == 2'b10)) |-> (out == in[2])
    );

    // With sel=3 and enable high, output follows in[3].
    check_sel_3_routes_in3: assert property (
        @($global_clock) (enable && (sel == 2'b11)) |-> (out == in[3])
    );

endmodule