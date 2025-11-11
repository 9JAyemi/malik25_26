module fifo_buffer (
    input aclr,
    input clock,
    input [29:0] data,
    input rdreq,
    input wrreq,
    output [29:0] q,
    output [4:0] usedw
);

reg [29:0] buffer [31:0];
reg [4:0] usedw_reg;
reg [4:0] usedw_next;
reg [4:0] usedw_next_next;
reg [4:0] usedw_next_next_next;
reg [29:0] q_reg;
reg [29:0] q_next;
reg [29:0] q_next_next;
reg [29:0] q_next_next_next;
reg wr_en;
reg rd_en;
integer i;

always @(posedge clock or negedge aclr) begin
    if (~aclr) begin
        usedw_reg <= 0;
        q_reg <= 0;
        wr_en <= 0;
        rd_en <= 0;
    end
    else begin
        usedw_reg <= usedw_next_next_next;
        q_reg <= q_next_next_next;
        wr_en <= wrreq && (usedw_reg < 32);
        rd_en <= rdreq && (usedw_reg > 0);
    end
end

always @(posedge clock or negedge aclr) begin
    if (~aclr) begin
        usedw_next <= 0;
        usedw_next_next <= 0;
        usedw_next_next_next <= 0;
        q_next <= 0;
        q_next_next <= 0;
        q_next_next_next <= 0;
    end
    else begin
        usedw_next <= usedw_reg + wr_en - rd_en;
        usedw_next_next <= usedw_next;
        usedw_next_next_next <= usedw_next_next;
        q_next <= buffer[0];
        q_next_next <= q_next;
        q_next_next_next <= q_next_next;
    end
end

always @(posedge clock or negedge aclr) begin
    if (~aclr) begin
        buffer[0] <= 0;
    end
    else begin
        if (wr_en) begin
            buffer[usedw_reg] <= data;
        end
        if (rd_en) begin
            buffer[usedw_reg - 1] <= 0;
        end
        for (i = 1; i < 32; i = i + 1) begin
            buffer[i] <= buffer[i-1];
        end
    end
end

assign q = q_reg;
assign usedw = usedw_reg;

endmodule