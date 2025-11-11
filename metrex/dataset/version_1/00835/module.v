
module	zipdiv(i_clk, i_reset, i_wr, i_signed, i_numerator, i_denominator,
		o_busy, o_valid, o_err, o_quotient, o_flags);
	parameter		BW=32, LGBW = 5;
	input	wire		i_clk, i_reset;
	input	wire		i_wr, i_signed;
	input	wire [(BW-1):0]	i_numerator, i_denominator;
	output	reg		o_busy, o_valid, o_err;
	output	reg [(BW-1):0]	o_quotient;
	output	wire	[3:0]	o_flags;

	reg			r_busy;
	reg	[(2*BW-2):0]	r_divisor;
	reg	[(BW-1):0]	r_dividend;
	wire	[(BW):0]	diff; assign	diff = r_dividend - r_divisor[(BW-1):0];

	reg		r_sign, pre_sign, r_z, r_c, last_bit;
	reg	[(LGBW-1):0]	r_bit;
	reg	zero_divisor;

	initial	r_busy = 1'b0;
	always @(posedge i_clk)
		if (i_reset)
			r_busy <= 1'b0;
		else if (i_wr)
			r_busy <= 1'b1;
		else if ((last_bit)||(zero_divisor))
			r_busy <= 1'b0;

	initial	o_busy = 1'b0;
	always @(posedge i_clk)
		if (i_reset)
			o_busy <= 1'b0;
		else if (i_wr)
			o_busy <= 1'b1;
		else if (((last_bit)&&(!r_sign))||(zero_divisor))
			o_busy <= 1'b0;
		else if (!r_busy)
			o_busy <= 1'b0;

	initial	zero_divisor = 1'b0;
	always @(posedge i_clk)
		if (i_reset)
			zero_divisor <= 1'b0;
		else if (i_wr)
			zero_divisor <= (i_denominator == 0);
		else if (!r_busy)
			zero_divisor <= 1'b0;

	initial	o_valid = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_valid <= 1'b0;
	else if (r_busy)
	begin
		if ((last_bit)||(zero_divisor))
			o_valid <= (zero_divisor)||(!r_sign);
	end else if (r_sign)
	begin
		o_valid <= (!zero_divisor); end else
		o_valid <= 1'b0;

	initial	o_err = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		o_err <= 1'b0;
	else if (o_valid)
		o_err <= 1'b0;
	else if (((r_busy)||(r_sign))&&(zero_divisor))
		o_err <= 1'b1;
	else
		o_err <= 1'b0;

	initial	r_bit = 0;
	always @(posedge i_clk)
	if (i_reset)
		r_bit <= 0;
	else if ((r_busy)&&(!pre_sign))
		r_bit <= r_bit + 1'b1;
	else
		r_bit <= 0;

	initial	last_bit = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		last_bit <= 1'b0;
	else if (r_busy)
		last_bit <= (r_bit == {(LGBW){1'b1}}-1'b1);
	else
		last_bit <= 1'b0;

	initial	pre_sign = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		pre_sign <= 1'b0;
	else if (i_wr)
		pre_sign <= (i_signed)&&((i_numerator[BW-1])||(i_denominator[BW-1]));
	else
		pre_sign <= 1'b0;

	initial	r_z = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		r_z <= 1'b0;
	else if((r_busy)&&(r_divisor[(2*BW-2):(BW)] == 0)&&(!diff[BW]))
			r_z <= 1'b0;
	else if (i_wr)
		r_z <= 1'b1;

	initial	r_dividend = 0;
	always @(posedge i_clk)
	if (i_reset)
		r_dividend <= 0;
	else if (pre_sign)
	begin
		if (r_dividend[BW-1])
			r_dividend <= -r_dividend;
		end else if((r_busy)&&(r_divisor[(2*BW-2):(BW)]==0)&&(!diff[BW]))
		r_dividend <= diff[(BW-1):0];
	else if (!r_busy)
		r_dividend <=  i_numerator;

	initial	r_divisor = 0;
	always @(posedge i_clk)
	if (i_reset)
		r_divisor <= 0;
	else if (pre_sign)
	begin
		if (r_divisor[(2*BW-2)])
			r_divisor[(2*BW-2):(BW-1)]
				<= -r_divisor[(2*BW-2):(BW-1)];
	end else if (r_busy)
		r_divisor <= { 1'b0, r_divisor[(2*BW-2):1] };
	else
		r_divisor <= {  i_denominator, {(BW-1){1'b0}} };

	initial	r_sign = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		r_sign <= 1'b0;
	else if (pre_sign)
		r_sign <= ((r_divisor[(2*BW-2)])^(r_dividend[(BW-1)]));
	else if (r_busy)
		r_sign <= (r_sign)&&(!zero_divisor);
	else
		r_sign <= 1'b0;

	initial	o_quotient = 0;
	always @(posedge i_clk)
	if (i_reset)
		o_quotient <= 0;
	else if (r_busy)
	begin
		o_quotient <= { o_quotient[(BW-2):0], 1'b0 };
		if ((r_divisor[(2*BW-2):(BW)] == 0)&&(!diff[BW]))
			o_quotient[0] <= 1'b1;
	end else if (r_sign)
		o_quotient <= -o_quotient;
	else
		o_quotient <= 0;

	initial	r_c = 1'b0;
	always @(posedge i_clk)
	if (i_reset)
		r_c <= 1'b0;
	else
		r_c <= (r_busy)&&((diff == 0)||(r_dividend == 0));

	wire	w_n;
	assign w_n = o_quotient[(BW-1)];

	assign o_flags = { 1'b0, w_n, r_c, r_z };

`ifdef	FORMAL
	reg	f_past_valid;
	initial	f_past_valid = 0;
	always @(posedge i_clk)
		f_past_valid <= 1'b1;

`ifdef	DIV
`define	ASSUME	assume
`else
`define	ASSUME	assert
`endif

	initial	`ASSUME(i_reset);
	always @(*)
	if (!f_past_valid)
		`ASSUME(i_reset);

	always @(posedge i_clk)
	if ((!f_past_valid)||($past(i_reset)))
	begin
		assert(!o_busy);
		assert(!o_valid);
		assert(!o_err);
		assert(!r_busy);
		assert(!zero_divisor);
		assert(r_bit==0);
		assert(!last_bit);
		assert(!pre_sign);
		assert(!r_z);
		assert(r_dividend==0);
		assert(o_quotient==0);
		assert(!r_c);
		assert(r_divisor==0);

		`ASSUME(!i_wr);
	end

	always @(*)
	if (o_busy)
		`ASSUME(!i_wr);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(o_busy))&&(!o_busy))
	begin
		assert(o_valid);
	end

	always @(*)
	if (o_err)
		assert(o_valid);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_wr)))
		assert(!pre_sign);
	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(i_wr))&&($past(i_signed))
			&&(|$past({i_numerator[BW-1],i_denominator[BW-1]})))
		assert(pre_sign);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(i_wr)))
		assert(o_busy);

	always @(posedge i_clk)
	if ((f_past_valid)&&($past(o_valid)))
		assert(!o_valid);

	always @(*)
	if ((o_valid)&&(!o_err))
		assert(r_z == ((o_quotient == 0)? 1'b1:1'b0));

	always @(*)
	if ((o_valid)&&(!o_err))
		assert(w_n == o_quotient[BW-1]);

	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(r_busy))&&(!$past(i_wr)))
		assert(!o_busy);
	always @(posedge i_clk)
		assert((!o_busy)||(!o_valid));
	always @(posedge i_clk)
	if(o_busy) `ASSUME(!i_wr);
	always @(*)
		if(r_busy) assert(o_busy);

	reg	[BW:0]	f_bits_set;
	always @(posedge i_clk)
	if (i_reset)
		f_bits_set <= 0;
	else if (i_wr)
		f_bits_set <= 0;
	else if ((r_busy)&&(!pre_sign))
		f_bits_set <= { f_bits_set[BW-1:0], 1'b1 };

	always @(*)
	if ((o_valid)&&(!o_err))
		assert((!f_bits_set[BW])&&(&f_bits_set[BW-1:0]));


	always @(posedge i_clk)
	if ((f_past_valid)&&(!$past(i_reset))&&($past(r_busy))
		&&($past(r_divisor[2*BW-2:BW])==0))
	begin
		if ($past(r_divisor) == 0)
			assert(o_err);
		else if ($past(pre_sign))
		begin
			if ($past(r_dividend[BW-1]))
				assert(r_dividend == -$past(r_dividend));
			if ($past(r_divisor[(2*BW-2)]))
			begin
				assert(r_divisor[(2*BW-2):(BW-1)]
					== -$past(r_divisor[(2*BW-2):(BW-1)]));
				assert(r_divisor[BW-2:0] == 0);
			end
		end else begin
			if (o_quotient[0])
				assert(r_dividend == $past(diff));
			else
				assert(r_dividend == $past(r_dividend));

			assert(r_divisor[2*BW-2]==0);
			assert(r_divisor[2*BW-3:0]==$past(r_divisor[2*BW-2:1]));
		end
		if ($past(r_dividend) >= $past(r_divisor[BW-1:0]))
			assert(o_quotient[0]);
		else
			assert(!o_quotient[0]);
	end
`endif
endmodule
