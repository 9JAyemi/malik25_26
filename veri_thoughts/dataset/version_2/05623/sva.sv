module noise_generator_sva (
    input logic       clk,
    input logic [7:0] error,
    input logic [7:0] err_level,
    input logic [1:0] noise
);

    // External sampling clock; the RTL itself has no clock or reset.

    // When error changes, noise can only settle to 00 or error[1:0].
    check_error_change_noise_is_zero_or_lsb: assert property (
        @(posedge clk) $changed(error) |-> ((noise == 2'b00) || (noise == error[1:0]))
    );

    // If error changes to a value with low bits 00, noise must be 00.
    check_error_change_zero_lsb_forces_zero_noise: assert property (
        @(posedge clk) $changed(error) && (error[1:0] == 2'b00) |-> (noise == 2'b00)
    );

    // Any observed noise update must produce either 00 or error[1:0].
    check_noise_change_noise_is_zero_or_lsb: assert property (
        @(posedge clk) $changed(noise) |-> ((noise == 2'b00) || (noise == error[1:0]))
    );

    // A nonzero noise update must match the current error low bits.
    check_noise_change_nonzero_matches_error_lsb: assert property (
        @(posedge clk) $changed(noise) && (noise != 2'b00) |-> (noise == error[1:0])
    );

endmodule