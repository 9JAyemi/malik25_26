module encryption_module(
    input clk,
    input rst,
    input [99:0] in,
    input [31:0] key,
    output [99:0] out
);

    // Shift register with circular buffer architecture
    reg [4:0] shift_reg [99:0];
    reg [4:0] shift_reg_out;
    integer i;
    
    // Barrel shifter
    reg [99:0] barrel_shifter_out;
    
    // XOR gate
    reg [99:0] xor_out;
    
    // Control logic
    always @(posedge clk, posedge rst) begin
        if (rst) begin
            // Reset shift register
            for (i = 0; i < 100; i = i + 1) begin
                shift_reg[i] <= 0;
            end
            shift_reg_out <= 0;
            
            // Reset barrel shifter
            barrel_shifter_out <= 0;
            
            // Reset XOR gate
            xor_out <= 0;
        end else begin
            // Shift register
            for (i = 99; i > 0; i = i - 1) begin
                shift_reg[i] <= shift_reg[i-1];
            end
            shift_reg[0] <= in[99];
            shift_reg_out <= shift_reg[4];
            
            // Barrel shifter
            if (shift_reg_out == 0) begin
                barrel_shifter_out <= in;
            end else begin
                barrel_shifter_out <= {in[99-shift_reg_out+1:0], in[99:99-shift_reg_out+2]};
            end
            
            // XOR gate
            xor_out <= barrel_shifter_out ^ key;
        end
    end
    
    // Output
    assign out = xor_out;

endmodule