module dffsi_9 (
    input clk,
    input reset,
    input [8:0] init,
    input [8:0] d,
    output reg [8:0] q
);

    // Synthesis Attribute to keep hierarchy
     

    // Random initialization
    `ifdef RANDOM_INIT
        initial $random_init(q);
    `endif

    // Assertion for checking reset signal
    `ifdef CHK_RESET_EOS
        assert_quiescent_state #(0,1,0, "***ERROR ASSERT: reset still asserted at end of simulation")
            a0(.clk(clk), .reset_n(1'b1), .state_expr(reset), .check_value(1'b0), .sample_event(1'b0));
    `endif

    always @(posedge clk) begin
        if (!reset) begin
            q <= init;
        end else begin
            q <= d;
        end
    end

endmodule