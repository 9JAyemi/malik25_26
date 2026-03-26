module sm_clk_divider_sva
#(
    parameter integer shift  = 16,
    parameter integer bypass = 0
)
(
    input logic         clkIn,
    input logic         rst_n,
    input logic [3:0]   devide,
    input logic         enable,
    input logic         clkOut,
    input logic [31:0]  cntr
);

    // Counter must be zero whenever reset is asserted.
    check_counter_zero_during_reset: assert property (
        @(posedge clkIn)
        !rst_n |-> (cntr == 32'd0)
    );

    // Enabled cycles increment the counter by one.
    check_counter_increments_when_enabled: assert property (
        @(posedge clkIn) disable iff (!rst_n)
        enable |=> (cntr == ($past(cntr) + 32'd1))
    );

    // Disabled cycles hold the counter value.
    check_counter_holds_when_disabled: assert property (
        @(posedge clkIn) disable iff (!rst_n)
        !enable |=> $stable(cntr)
    );

    generate
        if (bypass != 0) begin : gen_bypass_asserts
            // Bypass mode forwards clkIn to clkOut at the sampled edge.
            check_clkout_bypass_matches_clkin: assert property (
                @(posedge clkIn) disable iff (!rst_n)
                (clkOut == clkIn)
            );
        end else begin : gen_divide_asserts
            // Divide mode drives clkOut from the selected counter bit.
            check_clkout_matches_selected_counter_bit: assert property (
                @(posedge clkIn) disable iff (!rst_n)
                ((shift + devide) < 32) |-> (clkOut == cntr[shift + devide])
            );

            // Reset drives the divided output low for any valid selected bit.
            check_clkout_low_during_reset: assert property (
                @(posedge clkIn)
                (!rst_n && ((shift + devide) < 32)) |-> (clkOut == 1'b0)
            );

            // With no count update, a stable select keeps clkOut stable.
            check_clkout_holds_when_disabled_and_select_stable: assert property (
                @(posedge clkIn) disable iff (!rst_n)
                !enable |=> (!$stable(devide) || $stable(clkOut))
            );
        end
    endgenerate

endmodule