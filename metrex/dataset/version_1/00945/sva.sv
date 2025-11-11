// SVA for Computer_System_Video_In_Subsystem_Edge_Detection_Subsystem_Edge_Detection_Router_Controller

// Bind module with concise, high-quality assertions and coverage
module edge_det_router_ctrl_sva (
  input  logic        clk,
  input  logic        reset_n,
  input  logic [1:0]  address,
  input  logic        chipselect,
  input  logic        write_n,
  input  logic [31:0] writedata,
  input  logic        out_port,
  input  logic [31:0] readdata,
  input  logic        data_out   // internal reg from DUT
);
  localparam logic [1:0] ADDR0 = 2'b00;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset_n)

  // Reset drives data_out low
  assert property (!reset_n |-> data_out == 1'b0);

  // out_port mirrors data_out
  assert property (out_port == data_out);

  // Read data format and decode
  // MSBs zero; LSB equals (address==0) & data_out
  assert property (readdata[31:1] == '0 && readdata[0] == ((address == ADDR0) && data_out));

  // Correct write behavior: write at ADDR0 updates data_out to writedata[0] next cycle
  assert property (chipselect && !write_n && address == ADDR0 |=> data_out == $past(writedata[0]));

  // No-write (or wrong address) holds data_out
  assert property (!(chipselect && !write_n && address == ADDR0) |=> data_out == $past(data_out));

  // Optional: readback after write reflects the just-written bit
  assert property (chipselect && !write_n && address == ADDR0
                   ##1 (address == ADDR0) |-> readdata[0] == $past(writedata[0]) && out_port == $past(writedata[0]));

  // ----------------
  // Functional coverage
  // ----------------

  // Reset pulse observed
  cover property (!reset_n ##1 reset_n);

  // Writes of 0 and 1 to ADDR0
  cover property (chipselect && !write_n && address == ADDR0 && writedata[0] == 1'b0);
  cover property (chipselect && !write_n && address == ADDR0 && writedata[0] == 1'b1);

  // Toggling data_out via writes
  cover property (chipselect && !write_n && address == ADDR0 && writedata[0] != data_out
                  ##1 data_out == $past(writedata[0]));

  // Reads at both decoded and non-decoded addresses
  cover property (address == ADDR0 && readdata[0] == data_out);
  cover property (address != ADDR0 && readdata[0] == 1'b0);

endmodule

bind Computer_System_Video_In_Subsystem_Edge_Detection_Subsystem_Edge_Detection_Router_Controller
  edge_det_router_ctrl_sva
  (
    .clk       (clk),
    .reset_n   (reset_n),
    .address   (address),
    .chipselect(chipselect),
    .write_n   (write_n),
    .writedata (writedata),
    .out_port  (out_port),
    .readdata  (readdata),
    .data_out  (data_out)
  );