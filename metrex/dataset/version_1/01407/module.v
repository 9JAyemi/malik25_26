module delay_module(
    input input_signal,
    input [1:0] delay_amount,
    input clk,
    output reg output_signal
);

reg [3:0] delay_counter;

always @(posedge clk) begin
    if(delay_amount == 0) begin
        delay_counter <= 1;
    end else if(delay_amount == 1) begin
        delay_counter <= 2;
    end else begin
        delay_counter <= 4;
    end
    
    if(delay_counter == 1) begin
        output_signal <= input_signal;
    end else if(delay_counter > 1) begin
        output_signal <= 0;
    end
    
    delay_counter <= delay_counter - 1;
end

endmodule