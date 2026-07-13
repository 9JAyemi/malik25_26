module memory_protection_blocks_sva #(
    parameter logic [31:0] start_address = 32'h00000000,
    parameter logic [31:0] end_address   = 32'h000000FF
) (
    input  logic        clk,
    input  logic [31:0] in1,
    input  logic        in2,
    input  logic        out
);
    // Convenience predicate for address in range [start_address, end_address]
    logic in_range;
    assign in_range = (in1 >= start_address) && (in1 <= end_address);

    // out must equal (in_range && in2)
    check_out_matches_function: assert property (
        @(posedge clk) out == (in_range && (in2 == 1'b1))
    );

    // When address is in range and in2 is high, out must be 1
    check_out_one_on_range_and_in2: assert property (
        @(posedge clk) (in_range && (in2 == 1'b1)) |-> (out == 1'b1)
    );

    // When in2 is low, out must be 0
    check_out_zero_when_in2_low: assert property (
        @(posedge clk) (in2 == 1'b0) |-> (out == 1'b0)
    );

    // When address is below start_address, out must be 0
    check_out_zero_when_below_range: assert property (
        @(posedge clk) (in1 < start_address) |-> (out == 1'b0)
    );

    // When address is above end_address, out must be 0
    check_out_zero_when_above_range: assert property (
        @(posedge clk) (in1 > end_address) |-> (out == 1'b0)
    );

    // At start_address with in2 high, out must be 1
    check_out_one_at_start_boundary: assert property (
        @(posedge clk) ((in1 == start_address) && (in2 == 1'b1)) |-> (out == 1'b1)
    );

    // At end_address with in2 high, out must be 1
    check_out_one_at_end_boundary: assert property (
        @(posedge clk) ((in1 == end_address) && (in2 == 1'b1)) |-> (out == 1'b1)
    );

    // If out is high, in2 must be high
    check_out_high_implies_in2_high: assert property (
        @(posedge clk) (out == 1'b1) |-> (in2 == 1'b1)
    );

    // If out is high, address must be within range
    check_out_high_implies_in_range: assert property (
        @(posedge clk) (out == 1'b1) |-> in_range
    );

    // If out is 0 while in2 is 1, address must be out of range
    check_out_zero_with_in2_high_implies_out_of_range: assert property (
        @(posedge clk) ((out == 1'b0) && (in2 == 1'b1)) |-> (!in_range)
    );
endmodule