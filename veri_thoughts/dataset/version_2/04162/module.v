module mux32(
    input wire [4:0] select,
    input wire [7:0] data_i00,
    input wire [7:0] data_i01,
    input wire [7:0] data_i02,
    input wire [7:0] data_i03,
    input wire [7:0] data_i04,
    input wire [7:0] data_i05,
    input wire [7:0] data_i06,
    input wire [7:0] data_i07,
    input wire [7:0] data_i08,
    input wire [7:0] data_i09,
    input wire [7:0] data_i10,
    input wire [7:0] data_i11,
    input wire [7:0] data_i12,
    input wire [7:0] data_i13,
    input wire [7:0] data_i14,
    input wire [7:0] data_i15,
    input wire [7:0] data_i16,
    input wire [7:0] data_i17,
    input wire [7:0] data_i18,
    input wire [7:0] data_i19,
    input wire [7:0] data_i20,
    input wire [7:0] data_i21,
    input wire [7:0] data_i22,
    input wire [7:0] data_i23,
    input wire [7:0] data_i24,
    input wire [7:0] data_i25,
    input wire [7:0] data_i26,
    input wire [7:0] data_i27,
    input wire [7:0] data_i28,
    input wire [7:0] data_i29,
    input wire [7:0] data_i30,
    input wire [7:0] data_i31,
    output reg [7:0] data_o
);

always @* begin
    case (select)
        5'd0: data_o = data_i00;
        5'd1: data_o = data_i01;
        5'd2: data_o = data_i02;
        5'd3: data_o = data_i03;
        5'd4: data_o = data_i04;
        5'd5: data_o = data_i05;
        5'd6: data_o = data_i06;
        5'd7: data_o = data_i07;
        5'd8: data_o = data_i08;
        5'd9: data_o = data_i09;
        5'd10: data_o = data_i10;
        5'd11: data_o = data_i11;
        5'd12: data_o = data_i12;
        5'd13: data_o = data_i13;
        5'd14: data_o = data_i14;
        5'd15: data_o = data_i15;
        5'd16: data_o = data_i16;
        5'd17: data_o = data_i17;
        5'd18: data_o = data_i18;
        5'd19: data_o = data_i19;
        5'd20: data_o = data_i20;
        5'd21: data_o = data_i21;
        5'd22: data_o = data_i22;
        5'd23: data_o = data_i23;
        5'd24: data_o = data_i24;
        5'd25: data_o = data_i25;
        5'd26: data_o = data_i26;
        5'd27: data_o = data_i27;
        5'd28: data_o = data_i28;
        5'd29: data_o = data_i29;
        5'd30: data_o = data_i30;
        5'd31: data_o = data_i31;
    endcase
end

endmodule