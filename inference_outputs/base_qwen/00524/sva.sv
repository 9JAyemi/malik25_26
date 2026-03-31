```systemverilog
module pwm_generator_sva (
    input logic clk,
    input logic rst_n,
    output logic pwm_out
);
    ///// Device reset /////
    // At reset assertion, pwm_out must be LOW.
    reset: assert property (
        @(posedge clk) !rst_n |-> (pwm_out == 1'b0)
    );

    ///// PWM output behavior /////
    // pwm_out toggles on each positive edge of the clock.
    toggle: assert property (
        @(posedge clk) disable iff (!rst_n) pwm_out == ~pwm_out
    );
endmodule
```