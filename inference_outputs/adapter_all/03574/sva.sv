module square_module_sva (
    input logic [3:0] num,
    input logic [7:0] square
);
    // Square equals the low 8 bits of num*num.
    check_square_matches_low8: assert property (
        @(posedge num[0]) square == (num * num)[7:0]
    );

    // For num==0, square must be 0.
    check_zero_input_zero_output: assert property (
        @(posedge num[0]) (num == 4'd0) |-> (square == 8'd0)
    );

    // For num==1, square must be 1.
    check_one_input_one_output: assert property (
        @(posedge num[0]) (num == 4'd1) |-> (square == 8'd1)
    );

    // For num==2, square must be 4.
    check_two_input_four_output: assert property (
        @(posedge num[0]) (num == 4'd2) |-> (square == 8'd4)
    );

    // For num==3, square must be 9.
    check_three_input_nine_output: assert property (
        @(posedge num[0]) (num == 4'd3) |-> (square == 8'd9)
    );

    // For num==4, square must be 16.
    check_four_input_sixteen_output: assert property (
        @(posedge num[0]) (num == 4'd4) |-> (square == 8'd16)
    );

    // For num==5, square must be 25.
    check_five_input_twentyfive_output: assert property (
        @(posedge num[0]) (num == 4'd5) |-> (square == 8'd25)
    );

    // For num==6, square must be 36.
    check_six_input_thirty6_output: assert property (
        @(posedge num[0]) (num == 4'd6) |-> (square == 8'd36)
    );

    // For num==7, square must be 49.
    check_seven_input_forty9_output: assert property (
        @(posedge num[0]) (num == 4'd7) |-> (square == 8'd49)
    );

    // For num==8, square must be 64.
    check_eight_input_sixty4_output: assert property (
        @(posedge num[0]) (num == 4'd8) |-> (square == 8'd64)
    );

    // For num==9, square must be 81.
    check_nine_input_eighty1_output: assert property (
        @(posedge num[0]) (num == 4'd9) |-> (square == 8'd81)
    );

    // For num==10, square must be 100.
    check_ten_input_onehundred_output: assert property (
        @(posedge num[0]) (num == 4'd10) |-> (square == 8'd100)
    );

    // For num==11, square must be 121.
    check_eleven_input_onehundredtwentyone_output: assert property (
        @(posedge num[0]) (num == 4'd11) |-> (square == 8'd121)
    );

    // For num==12, square must be 144.
    check_twelve_input_onehundredfourtyfour_output: assert property (
        @(posedge num[0]) (num == 4'd12) |-> (square == 8'd144)
    );

    // For num==13, square must be 169.
    check_thirteen_input_onehundredsixtynine_output: assert property (
        @(posedge num[0]) (num == 4'd13) |-> (square == 8'd169)
    );

    // For num==14, square must be 196.
    check_fourteen_input_onehundredninety6_output: assert property (
        @(posedge num[0]) (num == 4'd14) |-> (square == 8'd196)
    );

    // For num==15, square must be 225.
    check_fifteen_input_twohundredtwentyfive_output: assert property (
        @(posedge num[0]) (num == 4'd15) |-> (square == 8'd225)
    );
endmodule