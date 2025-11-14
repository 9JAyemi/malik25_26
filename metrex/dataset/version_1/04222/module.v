
module fifo_buffer
    (AS,
     out,
     wr_clk,
     in0);

    output [0:0] AS;
    output out;
    input wr_clk;
    input [0:0] in0;

    reg [1:0] buffer;
    reg [1:0] next_buffer;
    reg full;

    assign AS = full;
    assign out = buffer[0];

    always @ (posedge wr_clk) begin
        if (!full) begin
            next_buffer[1] <= buffer[0];
            next_buffer[0] <= in0;
        end else begin
            next_buffer <= buffer;
        end
    end

    always @ (buffer, full) begin
        full = (buffer[1] != 1'b0);
    end

    always @ (posedge wr_clk) begin
        buffer <= next_buffer;
    end

endmodule