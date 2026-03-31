module up_down_counter (
    input clk,
    input up_down,
    input load,
    input reset,
    output reg [3:0] count,
    input [3:0] data_in
);

    always @(posedge clk, posedge reset) begin
        if (reset) begin
            count <= 4'b0;
        end else if (load) begin
            count <= data_in;
        end else if (up_down) begin
            count <= count + 1;
        end else begin
            count <= count - 1;
        end
    end

endmodule