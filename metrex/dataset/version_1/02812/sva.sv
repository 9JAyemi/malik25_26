// SVA for timer. Bind this to the DUT.

module timer_sva #(
  parameter WIDTH = 64,
  parameter USE_2XCLK = 0,
  parameter S_WIDTH_A = 2
)(
  input  logic                   clk,
  input  logic                   clk2x,
  input  logic                   resetn,

  input  logic [S_WIDTH_A-1:0]   slave_address,
  input  logic [WIDTH-1:0]       slave_writedata,
  input  logic                   slave_read,
  input  logic                   slave_write,
  input  logic [WIDTH/8-1:0]     slave_byteenable,
  input  logic                   slave_waitrequest,
  input  logic [WIDTH-1:0]       slave_readdata,
  input  logic                   slave_readdatavalid,

  input  logic [WIDTH-1:0]       counter,
  input  logic [WIDTH-1:0]       counter2x,
  input  logic                   clock_sel
);

  // Async reset holds regs at 0
  assert property (@(posedge clk)   !resetn |-> (counter=='0 && clock_sel==1'b0));
  assert property (@(posedge clk2x) !resetn |-> (counter2x=='0));

  // 1x counter behavior
  assert property (@(posedge clk) disable iff (!resetn)
                   (slave_write) |=> (counter=='0));
  assert property (@(posedge clk) disable iff (!resetn)
                   (!slave_write) |=> (counter == $past(counter)+1));

  // 2x counter behavior
  assert property (@(posedge clk2x) disable iff (!resetn)
                   (slave_write) |=> (counter2x=='0));
  assert property (@(posedge clk2x) disable iff (!resetn)
                   (!slave_write) |=> (counter2x == $past(counter2x)+1));

  // clock_sel updates only on write, reflects reduction-or of writedata
  assert property (@(posedge clk) disable iff (!resetn)
                   (slave_write) |=> (clock_sel == (|$past(slave_writedata))));
  assert property (@(posedge clk) disable iff (!resetn)
                   (!slave_write) |=> (clock_sel == $past(clock_sel)));

  // Static and simple signal checks
  assert property (@(posedge clk) slave_waitrequest == 1'b0);
  assert property (@(posedge clk) slave_readdatavalid == slave_read);

  // Read-data mux correctness (check on both clocks)
  generate
    if (USE_2XCLK) begin
      assert property (@(posedge clk)
                       slave_readdata == (clock_sel ? counter2x : counter));
      assert property (@(posedge clk2x)
                       slave_readdata == (clock_sel ? counter2x : counter));
    end else begin
      assert property (@(posedge clk)   slave_readdata == counter);
      assert property (@(posedge clk2x) slave_readdata == counter);
    end
  endgenerate

  // Minimal functional coverage
  cover property (@(posedge clk)   !resetn ##1 resetn); // reset release
  cover property (@(posedge clk)   disable iff (!resetn)
                  slave_write &&  (|slave_writedata) ##1 clock_sel);
  cover property (@(posedge clk)   disable iff (!resetn)
                  slave_write && !(|slave_writedata) ##1 !clock_sel);
  cover property (@(posedge clk)   disable iff (!resetn)
                  !slave_write ##1 (counter == $past(counter)+1));
  cover property (@(posedge clk2x) disable iff (!resetn)
                  !slave_write ##1 (counter2x == $past(counter2x)+1));
  generate
    if (USE_2XCLK) begin
      cover property (@(posedge clk)   disable iff (!resetn)
                      clock_sel && slave_read && (slave_readdata==counter2x));
      cover property (@(posedge clk)   disable iff (!resetn)
                      !clock_sel && slave_read && (slave_readdata==counter));
    end else begin
      cover property (@(posedge clk)   disable iff (!resetn)
                      slave_read && (slave_readdata==counter));
    end
  endgenerate

endmodule

bind timer timer_sva #(
  .WIDTH(WIDTH),
  .USE_2XCLK(USE_2XCLK),
  .S_WIDTH_A(S_WIDTH_A)
) i_timer_sva (
  .clk(clk),
  .clk2x(clk2x),
  .resetn(resetn),
  .slave_address(slave_address),
  .slave_writedata(slave_writedata),
  .slave_read(slave_read),
  .slave_write(slave_write),
  .slave_byteenable(slave_byteenable),
  .slave_waitrequest(slave_waitrequest),
  .slave_readdata(slave_readdata),
  .slave_readdatavalid(slave_readdatavalid),
  .counter(counter),
  .counter2x(counter2x),
  .clock_sel(clock_sel)
);