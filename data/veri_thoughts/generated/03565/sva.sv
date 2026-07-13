module regSR_sva #(
    parameter INIT   = 1'bX,
    parameter SRMODE = 1'b0
) (
    input logic D,
    input logic CLK,
    input logic RST,
    input logic Q
);

    localparam bit INIT_KNOWN  = ((INIT === 1'b0) || (INIT === 1'b1));
    localparam bit DATA_MODE   = (SRMODE === 1'b0);
    localparam bit TOGGLE_MODE = (SRMODE === 1'b1);

    // Reset pulses must remain asserted until a clock edge.
    env_reset_pulse_visible_at_clk: assume property (
        @(posedge RST) 1'b1 |=> @(posedge CLK) RST
    );

    generate
        if (INIT_KNOWN) begin : gen_known_init
            // After a sampled reset cycle, Q is held at INIT at the next clock sample.
            check_reset_forces_init: assert property (
                @(posedge CLK) $past(RST) |-> (Q === INIT)
            );
        end
    endgenerate

    generate
        if (DATA_MODE) begin : gen_data_mode
            // In data mode, each non-reset clock loads the previous sampled D into Q.
            check_data_mode_captures_d: assert property (
                @(posedge CLK) disable iff (RST) !$past(RST) |-> (Q === $past(D))
            );
        end
        else if (TOGGLE_MODE) begin : gen_toggle_mode
            // In toggle mode, each non-reset clock inverts Q.
            check_toggle_mode_toggles_q: assert property (
                @(posedge CLK) disable iff (RST) !$past(RST) |-> (Q === ~$past(Q))
            );
        end
    endgenerate

endmodule