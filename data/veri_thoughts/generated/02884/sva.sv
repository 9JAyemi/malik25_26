module s7_sva (
    input logic [5:0] stage1_input,
    input logic [3:0] stage1_output
);
    // Combinational S-box; no clock/reset in RTL; assertions sampled on $global_clock with no reset.

    // Output must match mapping when input is 0.
    check_map_0: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd0) |-> (stage1_output == 4'd4));
    // Output must match mapping when input is 1.
    check_map_1: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd1) |-> (stage1_output == 4'd13));
    // Output must match mapping when input is 2.
    check_map_2: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd2) |-> (stage1_output == 4'd11));
    // Output must match mapping when input is 3.
    check_map_3: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd3) |-> (stage1_output == 4'd0));
    // Output must match mapping when input is 4.
    check_map_4: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd4) |-> (stage1_output == 4'd2));
    // Output must match mapping when input is 5.
    check_map_5: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd5) |-> (stage1_output == 4'd11));
    // Output must match mapping when input is 6.
    check_map_6: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd6) |-> (stage1_output == 4'd14));
    // Output must match mapping when input is 7.
    check_map_7: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd7) |-> (stage1_output == 4'd7));
    // Output must match mapping when input is 8.
    check_map_8: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd8) |-> (stage1_output == 4'd15));
    // Output must match mapping when input is 9.
    check_map_9: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd9) |-> (stage1_output == 4'd4));
    // Output must match mapping when input is 10.
    check_map_10: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd10) |-> (stage1_output == 4'd0));
    // Output must match mapping when input is 11.
    check_map_11: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd11) |-> (stage1_output == 4'd9));
    // Output must match mapping when input is 12.
    check_map_12: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd12) |-> (stage1_output == 4'd8));
    // Output must match mapping when input is 13.
    check_map_13: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd13) |-> (stage1_output == 4'd1));
    // Output must match mapping when input is 14.
    check_map_14: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd14) |-> (stage1_output == 4'd13));
    // Output must match mapping when input is 15.
    check_map_15: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd15) |-> (stage1_output == 4'd10));
    // Output must match mapping when input is 16.
    check_map_16: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd16) |-> (stage1_output == 4'd3));
    // Output must match mapping when input is 17.
    check_map_17: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd17) |-> (stage1_output == 4'd14));
    // Output must match mapping when input is 18.
    check_map_18: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd18) |-> (stage1_output == 4'd12));
    // Output must match mapping when input is 19.
    check_map_19: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd19) |-> (stage1_output == 4'd3));
    // Output must match mapping when input is 20.
    check_map_20: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd20) |-> (stage1_output == 4'd9));
    // Output must match mapping when input is 21.
    check_map_21: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd21) |-> (stage1_output == 4'd5));
    // Output must match mapping when input is 22.
    check_map_22: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd22) |-> (stage1_output == 4'd7));
    // Output must match mapping when input is 23.
    check_map_23: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd23) |-> (stage1_output == 4'd12));
    // Output must match mapping when input is 24.
    check_map_24: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd24) |-> (stage1_output == 4'd5));
    // Output must match mapping when input is 25.
    check_map_25: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd25) |-> (stage1_output == 4'd2));
    // Output must match mapping when input is 26.
    check_map_26: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd26) |-> (stage1_output == 4'd10));
    // Output must match mapping when input is 27.
    check_map_27: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd27) |-> (stage1_output == 4'd15));
    // Output must match mapping when input is 28.
    check_map_28: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd28) |-> (stage1_output == 4'd6));
    // Output must match mapping when input is 29.
    check_map_29: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd29) |-> (stage1_output == 4'd8));
    // Output must match mapping when input is 30.
    check_map_30: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd30) |-> (stage1_output == 4'd1));
    // Output must match mapping when input is 31.
    check_map_31: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd31) |-> (stage1_output == 4'd6));
    // Output must match mapping when input is 32.
    check_map_32: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd32) |-> (stage1_output == 4'd1));
    // Output must match mapping when input is 33.
    check_map_33: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd33) |-> (stage1_output == 4'd6));
    // Output must match mapping when input is 34.
    check_map_34: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd34) |-> (stage1_output == 4'd4));
    // Output must match mapping when input is 35.
    check_map_35: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd35) |-> (stage1_output == 4'd11));
    // Output must match mapping when input is 36.
    check_map_36: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd36) |-> (stage1_output == 4'd11));
    // Output must match mapping when input is 37.
    check_map_37: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd37) |-> (stage1_output == 4'd13));
    // Output must match mapping when input is 38.
    check_map_38: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd38) |-> (stage1_output == 4'd13));
    // Output must match mapping when input is 39.
    check_map_39: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd39) |-> (stage1_output == 4'd8));
    // Output must match mapping when input is 40.
    check_map_40: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd40) |-> (stage1_output == 4'd12));
    // Output must match mapping when input is 41.
    check_map_41: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd41) |-> (stage1_output == 4'd1));
    // Output must match mapping when input is 42.
    check_map_42: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd42) |-> (stage1_output == 4'd3));
    // Output must match mapping when input is 43.
    check_map_43: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd43) |-> (stage1_output == 4'd4));
    // Output must match mapping when input is 44.
    check_map_44: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd44) |-> (stage1_output == 4'd7));
    // Output must match mapping when input is 45.
    check_map_45: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd45) |-> (stage1_output == 4'd10));
    // Output must match mapping when input is 46.
    check_map_46: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd46) |-> (stage1_output == 4'd14));
    // Output must match mapping when input is 47.
    check_map_47: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd47) |-> (stage1_output == 4'd7));
    // Output must match mapping when input is 48.
    check_map_48: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd48) |-> (stage1_output == 4'd10));
    // Output must match mapping when input is 49.
    check_map_49: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd49) |-> (stage1_output == 4'd9));
    // Output must match mapping when input is 50.
    check_map_50: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd50) |-> (stage1_output == 4'd15));
    // Output must match mapping when input is 51.
    check_map_51: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd51) |-> (stage1_output == 4'd5));
    // Output must match mapping when input is 52.
    check_map_52: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd52) |-> (stage1_output == 4'd6));
    // Output must match mapping when input is 53.
    check_map_53: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd53) |-> (stage1_output == 4'd0));
    // Output must match mapping when input is 54.
    check_map_54: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd54) |-> (stage1_output == 4'd8));
    // Output must match mapping when input is 55.
    check_map_55: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd55) |-> (stage1_output == 4'd15));
    // Output must match mapping when input is 56.
    check_map_56: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd56) |-> (stage1_output == 4'd0));
    // Output must match mapping when input is 57.
    check_map_57: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd57) |-> (stage1_output == 4'd14));
    // Output must match mapping when input is 58.
    check_map_58: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd58) |-> (stage1_output == 4'd5));
    // Output must match mapping when input is 59.
    check_map_59: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd59) |-> (stage1_output == 4'd2));
    // Output must match mapping when input is 60.
    check_map_60: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd60) |-> (stage1_output == 4'd9));
    // Output must match mapping when input is 61.
    check_map_61: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd61) |-> (stage1_output == 4'd3));
    // Output must match mapping when input is 62.
    check_map_62: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd62) |-> (stage1_output == 4'd2));
    // Output must match mapping when input is 63.
    check_map_63: assert property (@($global_clock) disable iff (1'b0) (stage1_input == 6'd63) |-> (stage1_output == 4'd12));

    // If input is stable across samples, output must be stable across samples.
    check_stable_when_input_stable: assert property (@($global_clock) disable iff (1'b0) $stable(stage1_input) |-> $stable(stage1_output));

endmodule