module alt_vipitc131_common_sync_sva
#(
    parameter CLOCKS_ARE_SAME = 0,
    parameter WIDTH = 1
)
(
    input logic rst,
    input logic sync_clock,
    input logic [WIDTH-1:0] data_in,
    input logic [WIDTH-1:0] data_out
);

generate
    if (CLOCKS_ARE_SAME) begin : gen_same_clock

        // In passthrough mode, output matches input when reset is low.
        check_passthrough_data: assert property (
            @(posedge sync_clock) disable iff (rst)
                (data_out == data_in)
        );

        // In passthrough mode, output still matches input during reset.
        check_passthrough_data_in_reset: assert property (
            @(posedge sync_clock)
                rst |-> (data_out == data_in)
        );

    end else begin : gen_synchronizer

        // A sampled reset keeps the output at zero for the next two clocks.
        check_reset_flushes_pipeline: assert property (
            @(posedge sync_clock)
                rst |=> ((data_out == {WIDTH{1'b0}}) ##1 (data_out == {WIDTH{1'b0}}))
        );

        property p_two_cycle_sync_delay;
            logic [WIDTH-1:0] sampled_data;
            @(posedge sync_clock) disable iff (rst)
                (1'b1, sampled_data = data_in) |-> ##2 (data_out == sampled_data);
        endproperty

        // Without reset, output is the input delayed by two sync_clock edges.
        check_two_cycle_sync_delay: assert property (p_two_cycle_sync_delay);

    end
endgenerate

endmodule