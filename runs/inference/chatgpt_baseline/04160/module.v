module gray_shift_register (
    input CLK,
    input RST,
    input [7:0] data_in,
    input shift,
    input load,
    input select,
    output reg [7:0] shift_reg_out,
    output reg [7:0] counter_out,
    output reg [7:0] final_output
);

reg [7:0] gray_counter_out;
reg [7:0] shift_reg;

always @(posedge CLK) begin
    if (RST) begin
        gray_counter_out <= 8'b00000000;
        shift_reg <= 8'b00000000;
    end else begin
        gray_counter_out <= gray_counter_out + 1;
        if (load) begin
            shift_reg <= data_in;
        end else if (shift) begin
            shift_reg <= {shift_reg[6:0], 1'b0};
        end
    end
end

always @* begin
    counter_out = gray_counter_out ^ (gray_counter_out >> 1);
    shift_reg_out = shift_reg ^ (shift_reg >> 1);
    if (select) begin
        final_output = shift_reg_out;
    end else begin
        final_output = counter_out;
    end
end

endmodule