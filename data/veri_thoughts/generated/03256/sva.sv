module omsp_scan_mux_sva (
    input logic clk,
    input logic data_out,
    input logic data_in_scan,
    input logic data_in_func,
    input logic scan_mode
);

    // Output always matches the implemented mux expression.
    check_mux_function: assert property (
        @(posedge clk) data_out === (scan_mode ? data_in_scan : data_in_func)
    );

    // When scan mode is enabled, the scan input is selected.
    check_scan_path_selected: assert property (
        @(posedge clk) (scan_mode === 1'b1) |-> (data_out === data_in_scan)
    );

    // When scan mode is disabled, the functional input is selected.
    check_functional_path_selected: assert property (
        @(posedge clk) (scan_mode === 1'b0) |-> (data_out === data_in_func)
    );

    // If both inputs are equal, the output matches that common value.
    check_equal_inputs_passthrough: assert property (
        @(posedge clk) (data_in_scan === data_in_func) |-> (data_out === data_in_scan)
    );

endmodule