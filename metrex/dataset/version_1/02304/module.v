
module addr_gen(nrst, clk, wr_en, wr_inc, load_w2r, rd_inc, rd_step, addr_wr, addr_rd, wr_end);
    input nrst;
    input clk;
    input wr_en;
    input wr_inc;
    input load_w2r;
    input rd_inc;
    input [7:0] rd_step;
    output [17:0] addr_wr;
    output [17:0] addr_rd;
    output wr_end;
    
    wire [17:0] addr_wr;
    wire [17:0] addr_rd;
    wire [17:0] rd_step_ex;
    reg wr_end;
    wire wr_inc_sig;
    wire reach;
    
    // 写地址返回到读地址表示写满，实现预触发深度调整是触发后立即修改读地址到需要位置
    assign reach = (addr_wr == addr_rd);
    assign wr_inc_sig = wr_en & wr_inc & ~wr_end;
    
    assign rd_step_ex = {{11{rd_step[7]}}, rd_step[6:0]};
    
    // 写地址自增
    cnt #(18) u_wrcnt(.nrst(nrst), .clk(clk),
        .en(wr_inc_sig), .step(1), .load(0), .cin(0), .cnt(addr_wr));
    
    // 触发时设置读地址为写地址，否则自增或自减
    cnt #(18) u_rdcnt(.nrst(nrst), .clk(clk),
        .en(rd_inc), .step(rd_step_ex), .load(load_w2r), .cin(addr_wr), .cnt(addr_rd));
    
    // 生成采样完成信号，在停止采样时清除
    always @(posedge clk or negedge nrst) begin
        if (~nrst) begin
            wr_end <= 1'b0;
        end else if (reach) begin
            wr_end <= 1'b1;
        end else if (~wr_en) begin
            wr_end <= 1'b0;
        end
    end
endmodule
module cnt #(parameter WIDTH = 8)
(
    input nrst,
    input clk,
    input en,
    input [WIDTH-1:0] step,
    input load,
    input [WIDTH-1:0] cin,
    output reg [WIDTH-1:0] cnt
);

    always @(posedge clk or negedge nrst) begin
        if (~nrst) begin
            cnt <= 'b0;
        end else if (load) begin
            cnt <= cin;
        end else if (en) begin
            cnt <= cnt + step;
        end
    end

endmodule