module up_down_counter (
    input up_down,
    input load,
    input clock,
    input reset,
    output reg [3:0] count
);

    always @(posedge clock, negedge reset) begin
        if (reset == 0) begin
            count <= 4'b0000;
        end else if (load == 1) begin
            count <= 4'b0000;
        end else if (up_down == 1) begin
            count <= count + 4'b0001;
        end else begin
            count <= count - 4'b0001;
        end
    end

endmodule