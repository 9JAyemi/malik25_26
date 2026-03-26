module top_module_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [1:0] shift,
    input logic [3:0] in,
    input logic enable,
    input logic [1:0] pos,
    input logic [3:0] out
);

    function automatic logic [3:0] rotated_value(input logic [3:0] a, input logic [1:0] s);
        case (s)
            2'b00: rotated_value = a;
            2'b01: rotated_value = {a[2:0], a[3]};
            2'b10: rotated_value = {a[1:0], a[3:2]};
            2'b11: rotated_value = {a[0], a[3:1]};
        endcase
    endfunction

    function automatic logic [1:0] encoded_pos(input logic [3:0] v, input logic en);
        if (en) begin
            case (v)
                4'b0001: encoded_pos = 2'd0;
                4'b0010: encoded_pos = 2'd1;
                4'b0100: encoded_pos = 2'd2;
                4'b1000: encoded_pos = 2'd3;
                default: encoded_pos = 2'd0;
            endcase
        end
        else begin
            encoded_pos = 2'd0;
        end
    endfunction

    // pos matches the priority encoder result on the rotated input.
    check_pos_matches_priority_encoder: assert property (
        @(posedge clk)
        pos == encoded_pos(rotated_value(A, shift), enable)
    );

    // out matches the rotated value ORed with the nonzero-pos flag.
    check_out_matches_rtl_equation: assert property (
        @(posedge clk)
        out == (rotated_value(A, shift) | {3'b000, (encoded_pos(rotated_value(A, shift), enable) != 2'b00)})
    );

    // Disabling the encoder forces pos to zero.
    check_disable_clears_pos: assert property (
        @(posedge clk)
        !enable |-> (pos == 2'b00)
    );

    // Disabled operation leaves out equal to the rotated input value.
    check_disable_out_is_rotated_value: assert property (
        @(posedge clk)
        !enable |-> (out == rotated_value(A, shift))
    );

    // A nonzero pos only occurs for enabled 0010, 0100, or 1000 rotated inputs.
    check_nonzero_pos_requires_valid_pattern: assert property (
        @(posedge clk)
        (pos != 2'b00) |-> (enable &&
                            ((rotated_value(A, shift) == 4'b0010) ||
                             (rotated_value(A, shift) == 4'b0100) ||
                             (rotated_value(A, shift) == 4'b1000)))
    );

    // All other enabled rotated inputs produce a zero position.
    check_other_enabled_patterns_drive_zero_pos: assert property (
        @(posedge clk)
        (enable &&
         (rotated_value(A, shift) != 4'b0010) &&
         (rotated_value(A, shift) != 4'b0100) &&
         (rotated_value(A, shift) != 4'b1000)) |-> (pos == 2'b00)
    );

endmodule