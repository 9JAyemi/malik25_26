// SVA for led_controller – concise, high-quality checks and coverage
module led_controller_sva (
  input  logic        clk,
  input  logic        reset_n,
  input  logic [1:0]  address,
  input  logic        chipselect,
  input  logic        write_n,
  input  logic [31:0] writedata,
  input  logic [3:0]  out_port,
  input  logic [31:0] readdata,
  // internal
  input  logic [3:0]  data_out_i
);

  // Reset behavior
  assert property (@(posedge clk) !reset_n |-> (data_out_i == 4'h0));

  // out_port mirrors internal register
  assert property (@(posedge clk) out_port == data_out_i);

  // Valid write updates data_out on next cycle
  assert property (@(posedge clk) disable iff (!reset_n)
                   (chipselect && !write_n && (address==2'b00))
                   |=> (data_out_i == $past(writedata[3:0])));

  // Any change to data_out must be caused by a valid write (excluding reset)
  assert property (@(posedge clk) disable iff (!reset_n)
                   $changed(data_out_i) |-> $past(chipselect && !write_n && (address==2'b00)));

  // No write (or wrong address) => data_out holds value
  assert property (@(posedge clk) disable iff (!reset_n)
                   !(chipselect && !write_n && (address==2'b00)) |=> $stable(data_out_i));

  // Read mux correctness
  assert property (@(posedge clk)
                   readdata[3:0] == ((address==2'b00) ? data_out_i : 4'h0));
  assert property (@(posedge clk) readdata[31:4] == 28'h0);
  assert property (@(posedge clk) (address==2'b00) |-> (readdata[3:0] == out_port));

  // No Xs on outputs after reset
  assert property (@(posedge clk) disable iff (!reset_n)
                   (!$isunknown(out_port) && !$isunknown(readdata)));

  // Coverage: reset-release, all 16 writes observed on out_port and via read, and address!=0 read=0
  cover property (@(posedge clk) !reset_n ##1 reset_n);

  genvar v;
  generate
    for (v=0; v<16; v++) begin : C_WRITE_VALUES
      cover property (@(posedge clk) disable iff (!reset_n)
        (chipselect && !write_n && (address==2'b00) && (writedata[3:0]==v))
        ##1 (out_port==v)
        ##1 ((address==2'b00) && (readdata[3:0]==v)));
    end
  endgenerate

  cover property (@(posedge clk) disable iff (!reset_n)
                  (address!=2'b00) && (readdata==32'h0));

  // Back-to-back writes
  cover property (@(posedge clk) disable iff (!reset_n)
                  (chipselect && !write_n && (address==2'b00))
                  ##1 (chipselect && !write_n && (address==2'b00)));

endmodule

// Bind into the DUT (connect internal data_out)
bind led_controller led_controller_sva sva_led_controller (
  .clk       (clk),
  .reset_n   (reset_n),
  .address   (address),
  .chipselect(chipselect),
  .write_n   (write_n),
  .writedata (writedata),
  .out_port  (out_port),
  .readdata  (readdata),
  .data_out_i(data_out)
);