
create table section (
  sec_id serial primary key,
  course_id int not null,
  semester int not null,
  year int not null,
  building text,
  room_number int,
  time_slot_id int
);

create table teaches (
  id serial primary key,
  course_id int not null references section (course_id),
  sec_id int not null references section (sec_id),
)
