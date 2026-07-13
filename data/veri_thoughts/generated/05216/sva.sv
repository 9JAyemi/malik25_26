module full_synchronizer_sva #(
    parameter WIDTH = 1
)(
    input logic             clk,
    input logic             reset,
    input logic [WIDTH-1:0] datain,
    input logic [WIDTH-1:0] dataout
);
    // Clock: clk
    // Reset: reset is active-high and synchronous
    // Logic: sequential 2-bit shift register with combinational output

    // A reset cycle clears the output on the following cycle.
    check_reset_clears_output: assert property (
        @(posedge clk) reset |=> (dataout == {WIDTH{1'b0}})
    );

    // Bit 0 is a one-cycle delayed copy of datain[0].
    check_output_bit0_delay: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        !$past(reset) |-> (dataout[0] == $past(datain[0]))
    );

    generate
        if (WIDTH > 1) begin : gen_width_gt1
            // Bit 1 shifts in the prior value of output bit 0.
            check_output_bit1_shifts_bit0: assert property (
                @(posedge clk) disable iff (reset || $initstate)
                !$past(reset) |-> (dataout[1] == $past(dataout[0]))
            );

            // Bit 1 is a two-cycle delayed copy of datain[0].
            check_output_bit1_delay: assert property (
                @(posedge clk) disable iff (reset || $initstate)
                (!$past($initstate) && !$past(reset) && !$past(reset,2)) |-> (dataout[1] == $past(datain[0],2))
            );
        end

        if (WIDTH > 2) begin : gen_width_gt2
            // Bits above bit 1 are tied low by the 2-bit source.
            check_upper_bits_zero: assert property (
                @(posedge clk) (dataout[WIDTH-1:2] == {(WIDTH-2){1'b0}})
            );
        end
    endgenerate
endmodule

module pipeline_stall_sva #(
    parameter WIDTH = 1,
    parameter DEPTH = 2
)(
    input logic             clk,
    input logic             reset,
    input logic [WIDTH-1:0] datain,
    input logic [WIDTH-1:0] dataout
);
    // Clock: clk
    // Reset: reset is active-high and synchronous
    // Logic: sequential 2-bit shift register with combinational output

    // A reset cycle clears the output on the following cycle.
    check_reset_clears_output: assert property (
        @(posedge clk) reset |=> (dataout == {WIDTH{1'b0}})
    );

    // Bit 0 is a one-cycle delayed copy of datain[0].
    check_output_bit0_delay: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        !$past(reset) |-> (dataout[0] == $past(datain[0]))
    );

    generate
        if (WIDTH > 1) begin : gen_width_gt1
            // Bit 1 shifts in the prior value of output bit 0.
            check_output_bit1_shifts_bit0: assert property (
                @(posedge clk) disable iff (reset || $initstate)
                !$past(reset) |-> (dataout[1] == $past(dataout[0]))
            );

            // Bit 1 is a two-cycle delayed copy of datain[0].
            check_output_bit1_delay: assert property (
                @(posedge clk) disable iff (reset || $initstate)
                (!$past($initstate) && !$past(reset) && !$past(reset,2)) |-> (dataout[1] == $past(datain[0],2))
            );
        end

        if (WIDTH > 2) begin : gen_width_gt2
            // Bits above bit 1 are tied low by the 2-bit source.
            check_upper_bits_zero: assert property (
                @(posedge clk) (dataout[WIDTH-1:2] == {(WIDTH-2){1'b0}})
            );
        end
    endgenerate
endmodule