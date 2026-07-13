module reversed_gate_sva (
    input logic clk,
    input logic [4:0] ctrl,
    input logic [15:0] din,
    input logic [3:0] sel,
    input logic [31:0] dout
);
    // Clock: clk. No reset. Sequential partial updates to dout on posedge clk.

    // When case expr is 0, update dout[1:0] from din[1:0] and hold others.
    update_case_0: assert property (
        @(posedge clk)
        ((({(32)-((ctrl)*(sel))})+(1))-(2)) == 0 |=> 
            (dout[1:0] == $past(din[1:0])) &&
            (dout[31:2] == $past(dout[31:2]))
    );

    // When case expr is 31, update only dout[31] from din[0] and hold others.
    update_case_31: assert property (
        @(posedge clk)
        ((({(32)-((ctrl)*(sel))})+(1))-(2)) == 31 |=> 
            (dout[31] == $past(din[0])) &&
            (dout[30:0] == $past(dout[30:0]))
    );

    // When case expr is 30, update dout[31:30] from din[1:0] and hold others.
    update_case_30: assert property (
        @(posedge clk)
        ((({(32)-((ctrl)*(sel))})+(1))-(2)) == 30 |=> 
            (dout[31:30] == $past(din[1:0])) &&
            (dout[29:0] == $past(dout[29:0]))
    );

    // When case expr is outside 0..31, no slice updates; hold full dout.
    hold_when_no_case_match: assert property (
        @(posedge clk)
        !(((({(32)-((ctrl)*(sel))})+(1))-(2)) inside {[0:31]}) |=> 
            (dout == $past(dout))
    );

    // For case expr 1..29, update the targeted 2-bit slice and hold others.
    genvar gi_mid;
    generate
        for (gi_mid = 1; gi_mid <= 29; gi_mid++) begin : gen_mid_cases
            // When case expr equals gi_mid, update dout[gi_mid+1:gi_mid] and hold others.
            update_case_mid: assert property (
                @(posedge clk)
                ((({(32)-((ctrl)*(sel))})+(1))-(2)) == gi_mid |=> 
                    (dout[gi_mid+1:gi_mid] == $past(din[1:0])) &&
                    (dout[31:gi_mid+2] == $past(dout[31:gi_mid+2])) &&
                    (dout[gi_mid-1:0] == $past(dout[gi_mid-1:0]))
            );
        end
    endgenerate

endmodule