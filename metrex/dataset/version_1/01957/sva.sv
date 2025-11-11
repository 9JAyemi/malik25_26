// SVA checker for memory_generator
// Read-first, single-port synchronous RAM with uniform init
module memory_generator_sva
  #(parameter MEM_DEPTH = 1024,
    parameter INIT_VECTOR = 256'h0)
  (
    input  logic        clka,
    input  logic [9:0]  addra,
    input  logic        en,
    input  logic [35:0] data_in,
    input  logic [35:0] douta
  );

  default clocking cb @(posedge clka); endclocking

  // Reference model (mirrors DUT semantics: read-before-write)
  localparam logic [35:0] INIT_WORD = INIT_VECTOR[35:0];

  logic [35:0] model_mem [0:MEM_DEPTH-1];
  logic [35:0] exp_douta;
  bit          written   [0:MEM_DEPTH-1];

  integer i;
  initial begin
    for (i = 0; i < MEM_DEPTH; i++) begin
      model_mem[i] = INIT_WORD;
      written[i]   = 1'b0;
    end
  end

  always_ff @(posedge clka) begin
    exp_douta <= model_mem[addra];      // read-first
    if (en) begin
      model_mem[addra] <= data_in;      // write after read
      written[addra]   <= 1'b1;
    end
  end

  // Basic protocol / sanity checks
  assert property (addra < MEM_DEPTH)
    else $error("memory_generator: addra out of range (%0d >= %0d)", addra, MEM_DEPTH);

  assert property (!$isunknown({en, addra})))
    else $error("memory_generator: X/Z on en/addra");

  assert property (en |-> !$isunknown(data_in))
    else $error("memory_generator: X/Z on data_in when en=1");

  assert property (!$isunknown(douta)))
    else $error("memory_generator: X/Z on douta");

  // Functional correctness: DUT output must match reference model every cycle
  assert property (douta == exp_douta)
    else $error("memory_generator: douta mismatch. exp=%0h got=%0h", exp_douta, douta);

  // If an address has never been written since init, reading it must return INIT_WORD
  assert property (!written[addra] |-> douta == INIT_WORD)
    else $error("memory_generator: read of unwritten address did not return INIT_WORD");

  // Read-first on same-cycle write: during a write, current-cycle douta is pre-write data
  // (Covered by douta==exp_douta, but asserted explicitly for clarity)
  assert property (en |-> douta == exp_douta)
    else $error("memory_generator: not read-first on write cycle");

  // Coverage: key use-cases
  // 1) First read after init returns INIT_WORD
  cover property (!written[addra] && douta == INIT_WORD);

  // 2) Write then next-cycle read same address returns the written data
  cover property (en ##1 (addra == $past(addra)) && (douta == $past(data_in)));

  // 3) Back-to-back writes to same address
  cover property (en ##1 (en && addra == $past(addra)));

  // 4) Read-only cycle (no write)
  cover property (!en);

endmodule

// Bind into DUT
bind memory_generator memory_generator_sva #(.MEM_DEPTH(MEM_DEPTH), .INIT_VECTOR(INIT_VECTOR)) memory_generator_sva_i
(
  .clka   (clka),
  .addra  (addra),
  .en     (en),
  .data_in(data_in),
  .douta  (douta)
);