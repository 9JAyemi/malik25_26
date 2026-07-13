module myModule_sva (
    input logic v0e28cb,
    input logic v3ca442,
    input logic vcbab45
);
    // Output equals a & b on any input edge.
    check_and_function_on_input_edges: assert property (
        @(posedge v0e28cb or negedge v0e28cb or posedge v3ca442 or negedge v3ca442)
        disable iff (1'b0)
        vcbab45 == (v0e28cb & v3ca442)
    );

    // Output equals a & b on any output edge.
    check_and_function_on_output_edges: assert property (
        @(posedge vcbab45 or negedge vcbab45)
        disable iff (1'b0)
        vcbab45 == (v0e28cb & v3ca442)
    );

    // Output rising implies both inputs are HIGH.
    check_output_rise_requires_inputs_high: assert property (
        @(posedge vcbab45)
        disable iff (1'b0)
        (v0e28cb && v3ca442)
    );

    // Output falling implies at least one input is LOW.
    check_output_fall_requires_input_low: assert property (
        @(negedge vcbab45)
        disable iff (1'b0)
        (!v0e28cb || !v3ca442)
    );

    // Output change must be accompanied by a change on at least one input.
    check_output_change_requires_input_change: assert property (
        @(posedge vcbab45 or negedge vcbab45)
        disable iff (1'b0)
        ($changed(v0e28cb) || $changed(v3ca442))
    );

    // If both inputs are unchanged, output must be unchanged.
    check_stable_inputs_keep_output_stable: assert property (
        @(posedge v0e28cb or negedge v0e28cb or posedge v3ca442 or negedge v3ca442 or posedge vcbab45 or negedge vcbab45)
        disable iff (1'b0)
        (($stable(v0e28cb) && $stable(v3ca442)) |-> $stable(vcbab45))
    );
endmodule