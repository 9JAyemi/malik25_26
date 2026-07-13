module up_down_counter (
    input clk,
    input reset,
    input load,
    input up_down,
    input [3:0] data_in,
    output reg [3:0] count_out
);

    always @(posedge clk) begin
        if (reset) begin
            count_out <= 4'b0;
        end else if (load) begin
            count_out <= data_in;
        end else if (up_down) begin
            count_out <= count_out + 1;
        end else begin
            count_out <= count_out - 1;
        end
    end

endmodule