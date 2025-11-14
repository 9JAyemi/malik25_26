// SVA checker for rw_manager_bitcheck
module rw_manager_bitcheck_sva (
  input  logic                          ck,
  input  logic                          reset_n,
  input  logic                          clear,
  input  logic                          enable,
  input  logic        [$bits(read_data)-1:0] read_data,
  input  logic        [$bits(read_data)-1:0] reference_data,
  input  logic        [$bits(mask)-1:0]      mask,
  input  logic        [$bits(read_data)/$bits(mask)-1:0] error_word,

  // internal DUT signals (bound)
  input  logic        [$bits(read_data)-1:0] read_data_r,
  input  logic                               enable_r,
  input  logic        [$bits(read_data)/$bits(mask)-1:0] error_compute
);
  // Derive sizes from ports to avoid param coupling
  localparam int NUMBER_OF_WORDS = $bits(mask);                 // 2 or 4
  localparam int DATA_BUS_SIZE   = $bits(read_data);
  localparam int DATA_WIDTH      = DATA_BUS_SIZE / NUMBER_OF_WORDS;
  localparam int AFI_RATIO       = NUMBER_OF_WORDS/2;

  // Sanity on supported config
  initial begin
    if (!(NUMBER_OF_WORDS == 2 || NUMBER_OF_WORDS == 4))
      $error("rw_manager_bitcheck_sva: Unsupported NUMBER_OF_WORDS=%0d", NUMBER_OF_WORDS);
  end

  default clocking cb @(posedge ck); endclocking

  // Async reset drives state to 0 while asserted
  a_reset_state: assert property (!reset_n |-> (error_word == {DATA_WIDTH{1'b0}}
                                             && read_data_r == {DATA_BUS_SIZE{1'b0}}
                                             && enable_r   == 1'b0));

  // Registered pipelines
  a_pipe_rdata: assert property (reset_n && $past(reset_n) |-> read_data_r == $past(read_data));
  a_pipe_en   : assert property (reset_n && $past(reset_n) |-> enable_r   == $past(enable));

  // Clear has priority (takes effect in the cycle after observed)
  a_clear: assert property (reset_n && $past(reset_n) && $past(clear) |-> error_word == {DATA_WIDTH{1'b0}});

  // Update/hold behavior (uses previous cycle's control due to enable_r)
  a_update: assert property (reset_n && $past(reset_n) && $past(!clear && enable_r)
                             |-> error_word == ($past(error_word) | $past(error_compute)));
  a_hold  : assert property (reset_n && $past(reset_n) && $past(!clear && !enable_r)
                             |-> error_word == $past(error_word));

  // No bit can clear unless clear/reset
  a_monotonic_or: assert property (reset_n && $past(reset_n) && !$past(clear)
                                   |-> (error_word | $past(error_word)) == error_word);

  // Combinational correctness of error_compute per bit
  genvar b;
  generate
    for (b = 0; b < DATA_WIDTH; b++) begin : g_ec
      if (AFI_RATIO == 2) begin : g4
        a_ec_eq: assert property (
          error_compute[b] ==
            (((read_data_r[b]                   ^ reference_data[b                  ]) & ~mask[0]) |
             ((read_data_r[b +     DATA_WIDTH ] ^ reference_data[b +     DATA_WIDTH]) & ~mask[1]) |
             ((read_data_r[b + 2 * DATA_WIDTH ] ^ reference_data[b + 2 * DATA_WIDTH]) & ~mask[2]) |
             ((read_data_r[b + 3 * DATA_WIDTH ] ^ reference_data[b + 3 * DATA_WIDTH]) & ~mask[3]))
        );
      end else begin : g2
        a_ec_eq: assert property (
          error_compute[b] ==
            (((read_data_r[b]                   ^ reference_data[b                  ]) & ~mask[0]) |
             ((read_data_r[b +     DATA_WIDTH ] ^ reference_data[b +     DATA_WIDTH]) & ~mask[1]))
        );
      end
      // Cover: a set bit propagates into error_word when enabled and not cleared
      c_set_bit: cover property (reset_n && $past(reset_n) &&
                                 $past(!clear && enable_r && error_compute[b] && !error_word[b]) ##1
                                 error_word[b]);
    end
  endgenerate

  // Mask all ones => no errors computed
  a_mask_all_ones_zero_ec: assert property ((&mask) |-> (error_compute == {DATA_WIDTH{1'b0}}));

  // Coverage: reset, clear, mask extremes
  c_reset_deassert: cover property ($fell(reset_n) ##1 $rose(reset_n));
  c_clear_event   : cover property (reset_n && $past(reset_n) && $past(!clear) && $past(|error_word) ##1 clear ##1 (error_word == {DATA_WIDTH{1'b0}}));
  c_mask_all_zero : cover property (reset_n && (mask == {NUMBER_OF_WORDS{1'b0}}));
  c_mask_all_one  : cover property (reset_n && (&mask));

endmodule

// Bind into the DUT
bind rw_manager_bitcheck rw_manager_bitcheck_sva
  i_rw_manager_bitcheck_sva (
    .ck(ck),
    .reset_n(reset_n),
    .clear(clear),
    .enable(enable),
    .read_data(read_data),
    .reference_data(reference_data),
    .mask(mask),
    .error_word(error_word),
    .read_data_r(read_data_r),
    .enable_r(enable_r),
    .error_compute(error_compute)
  );