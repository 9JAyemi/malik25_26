module mux2to1_assertions (
    input logic sel,
    input logic in0,
    input logic in1,
    input logic out
);

    // On sel rising, the sampled output matches the mux function.
    check_out_matches_mux_on_sel_rise: assert property (
        @(posedge sel) out === (sel ? in1 : in0)
    );

    // On sel falling, the sampled output matches the mux function.
    check_out_matches_mux_on_sel_fall: assert property (
        @(negedge sel) out === (sel ? in1 : in0)
    );

    // On in0 rising, the sampled output matches the mux function.
    check_out_matches_mux_on_in0_rise: assert property (
        @(posedge in0) out === (sel ? in1 : in0)
    );

    // On in0 falling, the sampled output matches the mux function.
    check_out_matches_mux_on_in0_fall: assert property (
        @(negedge in0) out === (sel ? in1 : in0)
    );

    // On in1 rising, the sampled output matches the mux function.
    check_out_matches_mux_on_in1_rise: assert property (
        @(posedge in1) out === (sel ? in1 : in0)
    );

    // On in1 falling, the sampled output matches the mux function.
    check_out_matches_mux_on_in1_fall: assert property (
        @(negedge in1) out === (sel ? in1 : in0)
    );

endmodule