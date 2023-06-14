get_time:
	cbmc --function check_get_time stateful.c

get_time_fail:
	cbmc --function check_get_time -DFAIL_BASE -DFAIL_STEP stateful.c

ten_calls:
	cbmc --function check_ten_calls stateful.c

ten_calls_fail:
	cbmc --function check_ten_calls -DFAIL_BASE -DFAIL_STEP stateful.c

ten_calls_replace:
	cbmc --function ten_calls_replace stateful.c

ten_calls_replace_nondet:
	cbmc --function ten_calls_replace_nondet --nondet-static stateful.c
