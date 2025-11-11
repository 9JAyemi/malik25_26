// SVA checker for memory_interface
module memory_interface_sva #(
  parameter MEM_SIZE  = 2**8,
  parameter MEM_WIDTH = 12
)(
  input logic                  clka,
  input logic                  wea,
  input logic [7:0]            addra,
  input logic [MEM_WIDTH-1:0]  dina,
  input logic [MEM_WIDTH-1:0]  douta
);

  default clocking cb @(posedge clka); endclocking

  // Static sanity on parameterization vs address width
  initial assert (MEM_SIZE <= (1<<$bits(addra)))
    else $error("MEM_SIZE exceeds addressable range");

  // Simple shadow model (read-old / write-new semantics)
  logic [MEM_WIDTH-1:0] shadow [0:MEM_SIZE-1];
  logic                 valid  [0:MEM_SIZE-1];

  logic [MEM_WIDTH-1:0] exp_dout;
  logic                 exp_valid;

  always_ff @(posedge clka) begin
    exp_dout  <= shadow[addra];   // read-old value
    exp_valid <= valid [addra];
    if (wea) begin
      shadow[addra] <= dina;      // write-new after read
      valid [addra] <= 1'b1;
    end
  end

  // Inputs known when used
  assert property (!$isunknown(addra) && !$isunknown(wea));
  assert property (wea |-> !$isunknown(dina));

  // Address in declared memory range
  assert property (addra < MEM_SIZE);

  // Read data must match model when location is known
  assert property (exp_valid |-> (douta == exp_dout));

  // No X on douta when reading a known location
  assert property (exp_valid |-> !$isunknown(douta));

  // Write -> next-cycle read of same address returns written data
  assert property ($past(wea) && (addra == $past(addra)) |-> (douta == $past(dina)));

  // Coverage
  cover property (wea);                                        // any write
  cover property (!wea && exp_valid);                          // read known location
  cover property (wea && exp_valid && (douta == exp_dout));    // read-during-write yields old data
  cover property (wea ##1 (addra == $past(addra)));            // write then address held
  cover property (wea ##1 (wea && addra == $past(addra)));     // back-to-back write same addr
  cover property (wea && (addra == '0));                       // low address
  cover property (wea && (addra == MEM_SIZE-1));               // high address

endmodule

// Bind into the DUT
bind memory_interface memory_interface_sva #(.MEM_SIZE(MEM_SIZE), .MEM_WIDTH(MEM_WIDTH))
  memory_interface_sva_i (.*);