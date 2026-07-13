module sseg_driver_sva (
    input logic clk,
    input logic [3:0] digit,
    input logic [1:0] sel,
    input logic [3:0] anode,
    input logic [6:0] cathode
);
    ///// Anode decode /////
    // sel==00 drives anode to 1110
    check_anode_sel00_map: assert property (
        @(posedge clk) disable iff (1'b0) (sel == 2'b00) |-> (anode == 4'b1110)
    );
    // sel==01 drives anode to 1101
    check_anode_sel01_map: assert property (
        @(posedge clk) disable iff (1'b0) (sel == 2'b01) |-> (anode == 4'b1101)
    );
    // sel==10 drives anode to 1011
    check_anode_sel10_map: assert property (
        @(posedge clk) disable iff (1'b0) (sel == 2'b10) |-> (anode == 4'b1011)
    );
    // sel==11 drives anode to 0111
    check_anode_sel11_map: assert property (
        @(posedge clk) disable iff (1'b0) (sel == 2'b11) |-> (anode == 4'b0111)
    );

    ///// Cathode decode /////
    // digit==0 maps to 0000001
    check_cathode_digit_0: assert property (
        @(posedge clk) disable iff (1'b0) (digit == 4'h0) |-> (cathode == 7'b0000001)
    );
    // digit==1 maps to 1001111
    check_cathode_digit_1: assert property (
        @(posedge clk) disable iff (1'b0) (digit == 4'h1) |-> (cathode == 7'b1001111)
    );
    // digit==2 maps to 0010010
    check_cathode_digit_2: assert property (
        @(posedge clk) disable iff (1'b0) (digit == 4'h2) |-> (cathode == 7'b0010010)
    );
    // digit==3 maps to 0000110
    check_cathode_digit_3: assert property (
        @(posedge clk) disable iff (1'b0) (digit == 4'h3) |-> (cathode == 7'b0000110)
    );
    // digit==4 maps to 1001100
    check_cathode_digit_4: assert property (
        @(posedge clk) disable iff (1'b0) (digit == 4'h4) |-> (cathode == 7'b1001100)
    );
    // digit==5 maps to 0100100
    check_cathode_digit_5: assert property (
        @(posedge clk) disable iff (1'b0) (digit == 4'h5) |-> (cathode == 7'b0100100)
    );
    // digit==6 maps to 0100000
    check_cathode_digit_6: assert property (
        @(posedge clk) disable iff (1'b0) (digit == 4'h6) |-> (cathode == 7'b0100000)
    );
    // digit==7 maps to 0001111
    check_cathode_digit_7: assert property (
        @(posedge clk) disable iff (1'b0) (digit == 4'h7) |-> (cathode == 7'b0001111)
    );
    // digit==8 maps to 0000000
    check_cathode_digit_8: assert property (
        @(posedge clk) disable iff (1'b0) (digit == 4'h8) |-> (cathode == 7'b0000000)
    );
    // digit==9 maps to 0000100
    check_cathode_digit_9: assert property (
        @(posedge clk) disable iff (1'b0) (digit == 4'h9) |-> (cathode == 7'b0000100)
    );
    // digit==A maps to 0001000
    check_cathode_digit_a: assert property (
        @(posedge clk) disable iff (1'b0) (digit == 4'ha) |-> (cathode == 7'b0001000)
    );
    // digit==B maps to 1100000
    check_cathode_digit_b: assert property (
        @(posedge clk) disable iff (1'b0) (digit == 4'hb) |-> (cathode == 7'b1100000)
    );
    // digit==C maps to 0110001
    check_cathode_digit_c: assert property (
        @(posedge clk) disable iff (1'b0) (digit == 4'hc) |-> (cathode == 7'b0110001)
    );
    // digit==D maps to 1000012 (1000010)
    check_cathode_digit_d: assert property (
        @(posedge clk) disable iff (1'b0) (digit == 4'hd) |-> (cathode == 7'b1000010)
    );
    // digit==E maps to 0110000
    check_cathode_digit_e: assert property (
        @(posedge clk) disable iff (1'b0) (digit == 4'he) |-> (cathode == 7'b0110000)
    );
    // digit==F maps to 0111000
    check_cathode_digit_f: assert property (
        @(posedge clk) disable iff (1'b0) (digit == 4'hf) |-> (cathode == 7'b0111000)
    );

    ///// Stability /////
    // Outputs hold when inputs do not change between cycles
    hold_on_stable_inputs: assert property (
        @(posedge clk) disable iff (1'b0) ($stable(sel) && $stable(digit)) |-> ($stable(anode) && $stable(cathode))
    );
endmodule