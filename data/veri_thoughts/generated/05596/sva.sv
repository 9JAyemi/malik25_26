module register_sva #(
    parameter int width = 1,
    parameter logic [width-1:0] init = {width{1'b0}}
) (
    input logic CLK,
    input logic RST,
    input logic EN,
    input logic [width-1:0] D_IN,
    input logic [width-1:0] Q_OUT
);

    // A sampled reset leaves Q_OUT at the init value by the next clock.
    check_reset_forces_init: assert property (
        @(posedge CLK) RST |=> (Q_OUT == init)
    );

    // With EN high, Q_OUT loads D_IN unless reset forces init between clocks.
    check_load_when_enabled: assert property (
        @(posedge CLK) disable iff (RST)
        EN |=> ((Q_OUT == $past(D_IN)) || (Q_OUT == init))
    );

    // With EN low, Q_OUT holds its value unless reset forces init between clocks.
    check_hold_when_disabled: assert property (
        @(posedge CLK) disable iff (RST)
        !EN |=> ((Q_OUT == $past(Q_OUT)) || (Q_OUT == init))
    );

endmodule