module NumIn_sva (
    input logic        clk,
    input logic [7:0]  addFlag,
    input logic [31:0] number,
    input logic [7:0]  btn_out
);

    // btn_out[0] increments number[3:0] modulo 16.
    check_nibble0_follows_btn0_rise: assert property (
        @(posedge clk) disable iff ($initstate)
        number[3:0] == ($past(number[3:0]) + {3'd0, $rose(btn_out[0])})
    );

    // btn_out[1] increments number[7:4] modulo 16.
    check_nibble1_follows_btn1_rise: assert property (
        @(posedge clk) disable iff ($initstate)
        number[7:4] == ($past(number[7:4]) + {3'd0, $rose(btn_out[1])})
    );

    // btn_out[2] increments number[11:8] modulo 16.
    check_nibble2_follows_btn2_rise: assert property (
        @(posedge clk) disable iff ($initstate)
        number[11:8] == ($past(number[11:8]) + {3'd0, $rose(btn_out[2])})
    );

    // btn_out[3] increments number[15:12] modulo 16.
    check_nibble3_follows_btn3_rise: assert property (
        @(posedge clk) disable iff ($initstate)
        number[15:12] == ($past(number[15:12]) + {3'd0, $rose(btn_out[3])})
    );

    // btn_out[4] increments number[19:16] modulo 16.
    check_nibble4_follows_btn4_rise: assert property (
        @(posedge clk) disable iff ($initstate)
        number[19:16] == ($past(number[19:16]) + {3'd0, $rose(btn_out[4])})
    );

    // btn_out[5] increments number[23:20] modulo 16.
    check_nibble5_follows_btn5_rise: assert property (
        @(posedge clk) disable iff ($initstate)
        number[23:20] == ($past(number[23:20]) + {3'd0, $rose(btn_out[5])})
    );

    // btn_out[6] increments number[27:24] modulo 16.
    check_nibble6_follows_btn6_rise: assert property (
        @(posedge clk) disable iff ($initstate)
        number[27:24] == ($past(number[27:24]) + {3'd0, $rose(btn_out[6])})
    );

    // btn_out[7] increments number[31:28] modulo 16.
    check_nibble7_follows_btn7_rise: assert property (
        @(posedge clk) disable iff ($initstate)
        number[31:28] == ($past(number[31:28]) + {3'd0, $rose(btn_out[7])})
    );

    // Without any debounced button rise, number must hold.
    check_number_stable_without_btn_rise: assert property (
        @(posedge clk) disable iff ($initstate)
        !($rose(btn_out[0]) || $rose(btn_out[1]) || $rose(btn_out[2]) || $rose(btn_out[3]) ||
          $rose(btn_out[4]) || $rose(btn_out[5]) || $rose(btn_out[6]) || $rose(btn_out[7]))
        |-> (number == $past(number))
    );

    // Any observed number change must come from a debounced button rise.
    check_number_change_requires_btn_rise: assert property (
        @(posedge clk) disable iff ($initstate)
        (number != $past(number))
        |-> ($rose(btn_out[0]) || $rose(btn_out[1]) || $rose(btn_out[2]) || $rose(btn_out[3]) ||
             $rose(btn_out[4]) || $rose(btn_out[5]) || $rose(btn_out[6]) || $rose(btn_out[7]))
    );

endmodule

bind NumIn NumIn_sva u_NumIn_sva (
    .clk(clk),
    .addFlag(addFlag),
    .number(number),
    .btn_out(btn_out)
);