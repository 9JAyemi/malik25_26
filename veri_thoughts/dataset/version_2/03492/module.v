module decoder_2to4_adder (
    input clk, 
    input [1:0] in,
    input ena,
    input cin,
    output reg [3:0] out,
    output reg cout
);

// Pipeline registers
reg [1:0] in_reg;
reg ena_reg;
reg cin_reg;

// 2-to-4 decoder
wire [3:0] dec_out;
// Corrected decoder logic
assign dec_out = ena ? (1 << in) : 4'b0000;

// Adder logic corrected
wire [3:0] add_out;
wire [3:0] add_in = {2'b00, in_reg}; // Ensure matching bit widths for addition
wire cout_temp; // Temporary carry-out

assign {cout_temp, add_out[1:0]} = add_in[1:0] + {2'b00, cin_reg};
assign add_out[3:2] = 2'b00; // Upper bits of add_out are not affected by addition


always @(posedge clk) begin
    in_reg <= in;
    ena_reg <= ena;
    cin_reg <= cin;
    
    if (ena_reg) begin
        out <= dec_out | add_out;
        cout <= cout_temp; 
    end else begin
        out <= 4'b0000;
        cout <= 0;
    end
end

endmodule
