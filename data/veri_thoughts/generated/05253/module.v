module priority_encoder (
    input [2:0] in,
    output reg [2:0] out
);

always @* begin
    case(in)
        3'b000: out = 3'b000;
        3'b001: out = 3'b001;
        3'b010: out = 3'b010;
        3'b011: out = 3'b011;
        3'b100: out = 3'b100;
        3'b101: out = 3'b101;
        default: out = 3'b111; // Output 111 if input is outside the range of 0 to 5
    endcase
end

endmodule

module tff_mux (
    input clk,    // Clocks are used in sequential circuits
    input d,      // Data input
    input [2:0] sel, // Select input to choose between 6 data inputs
    input [3:0] data0, // Six 4-bit data inputs
    input [3:0] data1,
    input [3:0] data2,
    input [3:0] data3,
    input [3:0] data4,
    input [3:0] data5,
    output reg [3:0] q // 4-bit output from the selected data input stored in a T flip-flop
);

// Priority encoder to select the appropriate data input
wire [2:0] encoded_sel;
priority_encoder pe(sel, encoded_sel);

// Combinational logic to select the appropriate 4-bit data input
wire [3:0] selected_data;
assign selected_data = (encoded_sel == 3'b000) ? data0 :
                       (encoded_sel == 3'b001) ? data1 :
                       (encoded_sel == 3'b010) ? data2 :
                       (encoded_sel == 3'b011) ? data3 :
                       (encoded_sel == 3'b100) ? data4 :
                       (encoded_sel == 3'b101) ? data5 :
                       4'b1111; // Output 1 if sel is outside the range of 0 to 5

// Combinational circuit to generate the appropriate T input for the flip-flop
wire t = (d == 1) ? ~q : q;

// T flip-flop to store the selected 4-bit data input
always @(posedge clk) begin
    if (t == 1) q <= ~q;
end

endmodule