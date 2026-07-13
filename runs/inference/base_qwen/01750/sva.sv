module MUX16_assertions (
    input logic CLK,
    input logic [3:0] select,
    input logic [7:0] data_i00,
    input logic [7:0] data_i01,
    input logic [7:0] data_i02,
    input logic [7:0] data_i03,
    input logic [7:0] data_i04,
    input logic [7:0] data_i05,
    input logic [7:0] data_i06,
    input logic [7:0] data_i07,
    input logic [7:0] data_i08,
    input logic [7:0] data_i09,
    input logic [7:0] data_i10,
    input logic [7:0] data_i11,
    input logic [7:0] data_i12,
    input logic [7:0] data_i13,
    input logic [7:0] data_i14,
    input logic [7:0] data_i15,
    output logic [7:0] data_o
);
    // MUX output must match the selected input
    mux_output: assert property (
        @(posedge CLK) disable iff (!CLK) data_o == {select == 4'b0000 ? data_i00 :
                                                   select == 4'b0001 ? data_i01 :
                                                   select == 4'b0010 ? data_i02 :
                                                   select == 4'b0011 ? data_i03 :
                                                   select == 4'b0100 ? data_i04 :
                                                   select == 4'b0101 ? data_i05 :
                                                   select == 4'b0110 ? data_i06 :
                                                   select == 4'b0111 ? data_i07 :
                                                   select == 4'b1000 ? data_i08 :
                                                   select == 4'b1001 ? data_i09 :
                                                   select == 4'b1010 ? data_i10 :
                                                   select == 4'b1011 ? data_i11 :
                                                   select == 4'b1100 ? data_i12 :
                                                   select == 4'b1101 ? data_i13 :
                                                   select == 4'b1110 ? data_i14 :
                                                   data_i15}
    );
endmodule