module s4_assertions (
    input logic clk,
    input logic [5:0] stage1_input,
    input logic [3:0] stage1_output
);

    // No clock or reset exists in the RTL; clk is a sampling clock for assertions.
    // stage1_input selects a combinational 6-bit to 4-bit lookup-table value.

    function automatic logic [3:0] s4_lut(input logic [5:0] in);
        case (in)
            6'd0:  s4_lut = 4'd7;
            6'd1:  s4_lut = 4'd13;
            6'd2:  s4_lut = 4'd13;
            6'd3:  s4_lut = 4'd8;
            6'd4:  s4_lut = 4'd14;
            6'd5:  s4_lut = 4'd11;
            6'd6:  s4_lut = 4'd3;
            6'd7:  s4_lut = 4'd5;
            6'd8:  s4_lut = 4'd0;
            6'd9:  s4_lut = 4'd6;
            6'd10: s4_lut = 4'd6;
            6'd11: s4_lut = 4'd15;
            6'd12: s4_lut = 4'd9;
            6'd13: s4_lut = 4'd0;
            6'd14: s4_lut = 4'd10;
            6'd15: s4_lut = 4'd3;
            6'd16: s4_lut = 4'd1;
            6'd17: s4_lut = 4'd4;
            6'd18: s4_lut = 4'd2;
            6'd19: s4_lut = 4'd7;
            6'd20: s4_lut = 4'd8;
            6'd21: s4_lut = 4'd2;
            6'd22: s4_lut = 4'd5;
            6'd23: s4_lut = 4'd12;
            6'd24: s4_lut = 4'd11;
            6'd25: s4_lut = 4'd1;
            6'd26: s4_lut = 4'd12;
            6'd27: s4_lut = 4'd10;
            6'd28: s4_lut = 4'd4;
            6'd29: s4_lut = 4'd14;
            6'd30: s4_lut = 4'd15;
            6'd31: s4_lut = 4'd9;
            6'd32: s4_lut = 4'd10;
            6'd33: s4_lut = 4'd3;
            6'd34: s4_lut = 4'd6;
            6'd35: s4_lut = 4'd15;
            6'd36: s4_lut = 4'd9;
            6'd37: s4_lut = 4'd0;
            6'd38: s4_lut = 4'd0;
            6'd39: s4_lut = 4'd6;
            6'd40: s4_lut = 4'd12;
            6'd41: s4_lut = 4'd10;
            6'd42: s4_lut = 4'd11;
            6'd43: s4_lut = 4'd1;
            6'd44: s4_lut = 4'd7;
            6'd45: s4_lut = 4'd13;
            6'd46: s4_lut = 4'd13;
            6'd47: s4_lut = 4'd8;
            6'd48: s4_lut = 4'd15;
            6'd49: s4_lut = 4'd9;
            6'd50: s4_lut = 4'd1;
            6'd51: s4_lut = 4'd4;
            6'd52: s4_lut = 4'd3;
            6'd53: s4_lut = 4'd5;
            6'd54: s4_lut = 4'd14;
            6'd55: s4_lut = 4'd11;
            6'd56: s4_lut = 4'd5;
            6'd57: s4_lut = 4'd12;
            6'd58: s4_lut = 4'd2;
            6'd59: s4_lut = 4'd7;
            6'd60: s4_lut = 4'd8;
            6'd61: s4_lut = 4'd2;
            6'd62: s4_lut = 4'd4;
            6'd63: s4_lut = 4'd14;
            default: s4_lut = 4'hx;
        endcase
    endfunction

    // Known inputs in the first quarter must match the lookup table.
    check_lookup_range_0_15: assert property (
        @(posedge clk)
        !$isunknown(stage1_input) &&
        (stage1_input <= 6'd15)
        |-> (stage1_output == s4_lut(stage1_input))
    );

    // Known inputs in the second quarter must match the lookup table.
    check_lookup_range_16_31: assert property (
        @(posedge clk)
        !$isunknown(stage1_input) &&
        (stage1_input >= 6'd16) && (stage1_input <= 6'd31)
        |-> (stage1_output == s4_lut(stage1_input))
    );

    // Known inputs in the third quarter must match the lookup table.
    check_lookup_range_32_47: assert property (
        @(posedge clk)
        !$isunknown(stage1_input) &&
        (stage1_input >= 6'd32) && (stage1_input <= 6'd47)
        |-> (stage1_output == s4_lut(stage1_input))
    );

    // Known inputs in the fourth quarter must match the lookup table.
    check_lookup_range_48_63: assert property (
        @(posedge clk)
        !$isunknown(stage1_input) &&
        (stage1_input >= 6'd48) && (stage1_input <= 6'd63)
        |-> (stage1_output == s4_lut(stage1_input))
    );

    // Every known input must produce a known output.
    check_known_input_has_known_output: assert property (
        @(posedge clk)
        !$isunknown(stage1_input)
        |-> !$isunknown(stage1_output)
    );

    // If the input is unchanged across samples, the output must also be unchanged.
    check_stable_input_keeps_output_stable: assert property (
        @(posedge clk)
        !$isunknown(stage1_input) &&
        !$isunknown($past(stage1_input)) &&
        (stage1_input == $past(stage1_input))
        |-> (stage1_output == $past(stage1_output))
    );

endmodule