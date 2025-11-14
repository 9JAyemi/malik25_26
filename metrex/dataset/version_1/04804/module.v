module soc_system_button_pio (
  // inputs:
  address,
  chipselect,
  clk,
  in_port,
  reset_n,
  write_n,
  writedata,

  // outputs:
  irq,
  readdata
);

  output irq;
  output [31:0] readdata;
  input [1:0] address;
  input chipselect;
  input clk;
  input [1:0] in_port;
  input reset_n;
  input write_n;
  input [31:0] writedata;

  wire clk_en;
  reg [1:0] d1_data_in;
  reg [1:0] d2_data_in;
  wire [1:0] data_in;
  reg [1:0] edge_capture;
  wire edge_capture_wr_strobe;
  wire [1:0] edge_detect;
  wire irq;
  reg [1:0] irq_mask;
  wire [1:0] read_mux_out;
  reg [31:0] readdata;

  assign clk_en = 1;

  // Multiplexer for readdata output
  assign read_mux_out = ({2 {(address == 0)}} & data_in) |
                        ({2 {(address == 2)}} & irq_mask) |
                        ({2 {(address == 3)}} & edge_capture);

  // Register for readdata output
  always @(posedge clk or negedge reset_n) begin
    if (reset_n == 0) begin
      readdata <= 0;
    end else if (clk_en) begin
      readdata <= {32'b0 | read_mux_out};
    end
  end

  // Assign data_in to in_port input
  assign data_in = in_port;

  // Register for irq_mask
  always @(posedge clk or negedge reset_n) begin
    if (reset_n == 0) begin
      irq_mask <= 0;
    end else if (chipselect && ~write_n && (address == 2)) begin
      irq_mask <= writedata[1:0];
    end
  end

  // Generate irq signal
  assign irq = |(edge_capture & irq_mask);

  // Generate edge_capture_wr_strobe signal
  assign edge_capture_wr_strobe = chipselect && ~write_n && (address == 3);

  // Register for edge_capture[0]
  always @(posedge clk or negedge reset_n) begin
    if (reset_n == 0) begin
      edge_capture[0] <= 0;
    end else if (clk_en) begin
      if (edge_capture_wr_strobe && writedata[0]) begin
        edge_capture[0] <= 0;
      end else if (edge_detect[0]) begin
        edge_capture[0] <= ~in_port[0];
      end
    end
  end

  // Register for edge_capture[1]
  always @(posedge clk or negedge reset_n) begin
    if (reset_n == 0) begin
      edge_capture[1] <= 0;
    end else if (clk_en) begin
      if (edge_capture_wr_strobe && writedata[1]) begin
        edge_capture[1] <= 0;
      end else if (edge_detect[1]) begin
        edge_capture[1] <= ~in_port[1];
      end
    end
  end

  // Registers for edge_detect
  always @(posedge clk or negedge reset_n) begin
    if (reset_n == 0) begin
      d1_data_in <= 0;
      d2_data_in <= 0;
    end else if (clk_en) begin
      d1_data_in <= data_in;
      d2_data_in <= d1_data_in;
    end
  end

  // Generate edge_detect signal
  assign edge_detect = ~d1_data_in & d2_data_in;

endmodule