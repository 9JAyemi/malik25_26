module add_subtract_sva (
    input logic        clk,
    input logic [3:0]  in,
    input logic [3:0]  out
);

    // Output must follow the RTL's add/subtract function for all input values.
    check_function_relation: assert property (
        @(posedge clk)
        out == ((in <= 4'd7) ? (in + 4'd3) : (in - 4'd3))
    );

    // Inputs 0 through 7 must take the add-by-3 branch.
    check_add_branch: assert property (
        @(posedge clk)
        (in <= 4'd7) |-> (out == (in + 4'd3))
    );

    // Inputs 8 through 15 must take the subtract-by-3 branch.
    check_subtract_branch: assert property (
        @(posedge clk)
        (in > 4'd7) |-> (out == (in - 4'd3))
    );

    // The lower boundary of the add branch must map 0 to 3.
    check_zero_boundary: assert property (
        @(posedge clk)
        (in == 4'd0) |-> (out == 4'd3)
    );

    // The upper boundary of the add branch must map 7 to 10.
    check_seven_boundary: assert property (
        @(posedge clk)
        (in == 4'd7) |-> (out == 4'd10)
    );

    // The lower boundary of the subtract branch must map 8 to 5.
    check_eight_boundary: assert property (
        @(posedge clk)
        (in == 4'd8) |-> (out == 4'd5)
    );

    // The upper input value must map 15 to 12.
    check_fifteen_boundary: assert property (
        @(posedge clk)
        (in == 4'd15) |-> (out == 4'd12)
    );

    // The computed output must always remain within the implemented numeric range.
    check_output_range: assert property (
        @(posedge clk)
        (out >= 4'd3) && (out <= 4'd12)
    );

endmodule