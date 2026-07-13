module mux_with_or_sva (
    input logic       clk,
    input logic [1:0] sel,
    input logic [3:0] data,
    input logic       w,
    input logic       x,
    input logic       y,
    input logic       z
);

    // No RTL clock or reset is present; clk is a sampling clock for these combinational checks.

    // w matches its combinational select behavior.
    check_w_function: assert property (
        @(posedge clk)
        w == ((sel == 2'b00) ? (data[0] | data[3]) : data[0])
    );

    // x matches its combinational select behavior.
    check_x_function: assert property (
        @(posedge clk)
        x == ((sel == 2'b01) ? (data[1] | data[3]) : data[1])
    );

    // y matches its combinational select behavior.
    check_y_function: assert property (
        @(posedge clk)
        y == ((sel == 2'b10) ? (data[0] | data[3]) : data[1])
    );

    // z matches its combinational select behavior.
    check_z_function: assert property (
        @(posedge clk)
        z == ((sel == 2'b11) ? (data[0] | data[3]) : data[0])
    );

    // For sel=00, only w uses the OR result.
    check_sel00_outputs: assert property (
        @(posedge clk)
        (sel == 2'b00) |-> ((w == (data[0] | data[3])) &&
                            (x == data[1]) &&
                            (y == data[1]) &&
                            (z == data[0]))
    );

    // For sel=01, only x uses the OR result.
    check_sel01_outputs: assert property (
        @(posedge clk)
        (sel == 2'b01) |-> ((w == data[0]) &&
                            (x == (data[1] | data[3])) &&
                            (y == data[1]) &&
                            (z == data[0]))
    );

    // For sel=10, only y uses the OR result derived from data[0].
    check_sel10_outputs: assert property (
        @(posedge clk)
        (sel == 2'b10) |-> ((w == data[0]) &&
                            (x == data[1]) &&
                            (y == (data[0] | data[3])) &&
                            (z == data[0]))
    );

    // For sel=11, only z uses the OR result derived from data[0].
    check_sel11_outputs: assert property (
        @(posedge clk)
        (sel == 2'b11) |-> ((w == data[0]) &&
                            (x == data[1]) &&
                            (y == data[1]) &&
                            (z == (data[0] | data[3])))
    );

    // When data[3] is low, all outputs reduce to their pass-through values.
    check_data3_low_passthrough: assert property (
        @(posedge clk)
        (data[3] == 1'b0) |-> ((w == data[0]) &&
                               (x == data[1]) &&
                               (y == ((sel == 2'b10) ? data[0] : data[1])) &&
                               (z == data[0]))
    );

    // When data[3] is high, the selected output must be driven high.
    check_data3_high_forces_selected_output: assert property (
        @(posedge clk)
        (data[3] == 1'b1) |-> (((sel != 2'b00) || (w == 1'b1)) &&
                               ((sel != 2'b01) || (x == 1'b1)) &&
                               ((sel != 2'b10) || (y == 1'b1)) &&
                               ((sel != 2'b11) || (z == 1'b1)))
    );

endmodule