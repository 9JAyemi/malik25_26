module resistive_touch_sva (
    input logic Xplus,
    input logic Xminus,
    input logic Yplus,
    input logic Yminus,
    input logic touch,
    input logic Xplus_prev,
    input logic Xminus_prev,
    input logic Yplus_prev,
    input logic Yminus_prev,
    input logic Xplus_curr,
    input logic Xminus_curr,
    input logic Yplus_curr,
    input logic Yminus_curr,
    input logic Xres,
    input logic Yres,
    input logic touch_reg
);

    // Curr registers mirror the settled input pin values.
    check_curr_mirrors_inputs: assert property (
        @(posedge Xplus or negedge Xplus or posedge Xminus or negedge Xminus or posedge Yplus or negedge Yplus or posedge Yminus or negedge Yminus)
        1'b1 |=> ({Xplus_curr, Xminus_curr, Yplus_curr, Yminus_curr} == {Xplus, Xminus, Yplus, Yminus})
    );

    // Prev registers shift in the prior curr values.
    check_prev_shifts_curr: assert property (
        @(posedge Xplus or negedge Xplus or posedge Xminus or negedge Xminus or posedge Yplus or negedge Yplus or posedge Yminus or negedge Yminus)
        1'b1 |=> ({Xplus_prev, Xminus_prev, Yplus_prev, Yminus_prev} ==
                  {$past(Xplus_curr), $past(Xminus_curr), $past(Yplus_curr), $past(Yminus_curr)})
    );

    // Prev registers reflect the input levels from one input event earlier.
    check_prev_tracks_prior_inputs: assert property (
        @(posedge Xplus or negedge Xplus or posedge Xminus or negedge Xminus or posedge Yplus or negedge Yplus or posedge Yminus or negedge Yminus)
        1'b1 |=> ({Xplus_prev, Xminus_prev, Yplus_prev, Yminus_prev} ==
                  {$past(Xplus), $past(Xminus), $past(Yplus), $past(Yminus)})
    );

    // Xres is the XOR of the captured previous X inputs.
    check_xres_from_prev: assert property (
        @(posedge Xplus or negedge Xplus or posedge Xminus or negedge Xminus or posedge Yplus or negedge Yplus or posedge Yminus or negedge Yminus)
        1'b1 |=> (Xres == (Xplus_prev ^ Xminus_prev))
    );

    // Yres is the XOR of the captured previous Y inputs.
    check_yres_from_prev: assert property (
        @(posedge Xplus or negedge Xplus or posedge Xminus or negedge Xminus or posedge Yplus or negedge Yplus or posedge Yminus or negedge Yminus)
        1'b1 |=> (Yres == (Yplus_prev ^ Yminus_prev))
    );

    // Xres matches the XOR of the prior curr X values.
    check_xres_from_prior_curr: assert property (
        @(posedge Xplus or negedge Xplus or posedge Xminus or negedge Xminus or posedge Yplus or negedge Yplus or posedge Yminus or negedge Yminus)
        1'b1 |=> (Xres == ($past(Xplus_curr) ^ $past(Xminus_curr)))
    );

    // Yres matches the XOR of the prior curr Y values.
    check_yres_from_prior_curr: assert property (
        @(posedge Xplus or negedge Xplus or posedge Xminus or negedge Xminus or posedge Yplus or negedge Yplus or posedge Yminus or negedge Yminus)
        1'b1 |=> (Yres == ($past(Yplus_curr) ^ $past(Yminus_curr)))
    );

    // touch_reg is the OR of the X and Y result bits.
    check_touch_reg_or_axes: assert property (
        @(posedge Xplus or negedge Xplus or posedge Xminus or negedge Xminus or posedge Yplus or negedge Yplus or posedge Yminus or negedge Yminus)
        1'b1 |=> (touch_reg == (Xres || Yres))
    );

    // The output touch directly mirrors touch_reg.
    check_touch_output_matches_reg: assert property (
        @(posedge Xplus or negedge Xplus or posedge Xminus or negedge Xminus or posedge Yplus or negedge Yplus or posedge Yminus or negedge Yminus)
        1'b1 |=> (touch == touch_reg)
    );

    // touch matches the OR of the captured previous-axis XORs.
    check_touch_from_prev_axes: assert property (
        @(posedge Xplus or negedge Xplus or posedge Xminus or negedge Xminus or posedge Yplus or negedge Yplus or posedge Yminus or negedge Yminus)
        1'b1 |=> (touch == ((Xplus_prev ^ Xminus_prev) || (Yplus_prev ^ Yminus_prev)))
    );

endmodule